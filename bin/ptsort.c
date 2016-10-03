/*-
 * Copyright (c) 2016 Dag-Erling Smørgrav
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote
 *    products derived from this software without specific prior written
 *    permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#ifdef HAVE_CONFIG_H
# include "config.h"
#endif

#include <err.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "aa_tree.h"

static int printprio;
static int quiet;
static int strict;
static int vlevel;

#define verbose(...)							\
	do {								\
		if (vlevel > 0)						\
			warnx(__VA_ARGS__);				\
	} while (0)

/*
 * Read a full line of text from a stream
 */
static const char *
freadline(FILE *f)
{
	static FILE *curf;
	static char *buf, *line, *next, *end;
	static size_t len, size, r;
	char *p, *q;

	if (buf == NULL) {
		/* first call, allocate buffer */
		size = 1024;
		if ((buf = malloc(size)) == NULL)
			err(1, "malloc()");
		next = line = end = buf;
		len = 0;
		curf = f;
	} else if (f != curf) {
		/* first call for new file, reset pointers */
		next = line = end = buf;
		len = 0;
		curf = f;
	}

	/*
	 * See if we already have a full line waiting.
	 */
	for (p = q = next; q < end; ++q) {
		if (*q == '\n') {
			next = q + 1;
			*q = '\0';
			return (p);
		}
	}

	/*
	 * Either our buffer is empty, or it only contains a partial line.
	 * We need to read more data into it, and possibly expand it.
	 * Start by moving the partial line (if any) up to the front.
	 */
	if (next > buf) {
		/* shift everything up by next - buf */
		len = end - next;
		memmove(buf, next, len);
		next = buf;
		end = buf + len;
	}
	for (;;) {
		if (len == size) {
			/* expand the buffer */
			size = size * 2;
			if ((buf = realloc(buf, size)) == NULL)
				err(1, "realloc()");
			end = buf + len;
		}
		if ((r = fread(end, 1, size - len, f)) == 0) {
			/* either EOF or error */
			if (len == 0) {
				/* we got nothing */
				return (NULL);
			}
			/* whatever is left */
			next = end + 1;
			*end = '\0';
			return (buf);
		}
		/* we got something, let's look for EOL */
		len += r;
		end += r;
		for (p = q = next; q < end; ++q) {
			if (*q == '\n') {
				next = q + 1;
				*q = '\0';
				return (p);
			}
		}
		/* nothing, loop around */
	}
}

/*
 * Quick character classification, assuming ASCII
 */
#define is_name(ch)							\
	((unsigned char)(ch) >= '!' && (unsigned char)(ch) <= '~')
#define is_number(ch)							\
	((unsigned char)(ch) >= '0' && (unsigned char)(ch) <= '9')
#define is_space(ch)							\
	((unsigned char)(ch) == ' ' || (unsigned char)(ch) == '\t')

/*
 * Nodes in the graph
 */
#define NAMELEN		 255

typedef struct pnode {
	char		 name[NAMELEN + 1];
	aa_tree		 pred;
	unsigned long	 prio;
} pnode;

static aa_tree nodes;
static unsigned long tnedges, tnnodes;

/*
 * Compare two nodes by their names.
 */
static aa_comparator pnode_namecmp = (aa_comparator)strcmp;

/*
 * Compare two nodes by their priorities.
 */
static int
pnode_priocmp(const void *av, const void *bv)
{
	const pnode *a = av;
	const pnode *b = bv;

	return (a->prio > b->prio ? 1 : a->prio < b->prio ? -1 : 0);
}

static int
pnodep_priocmp(const void *av, const void *bv)
{
	const pnode *const *a = av;
	const pnode *const *b = bv;

	return (pnode_priocmp(*a, *b));
}


/*
 * Allocate and initialize a new node.
 */
static pnode *
pnode_new(void)
{
	pnode *n;

	if ((n = calloc(1, sizeof *n)) == NULL)
		err(1, "calloc()");
	aa_init(&n->pred, pnode_namecmp);
	n->prio = 0;
	return (n);
}

#if 0
/*
 * Destroy a node.
 */
static void
pnode_destroy(pnode *n)
{

	aa_destroy(&n->pred);
	free(n);
}
#endif

/*
 * If the priority of a node is less than the given value, raise it to
 * that value and propagate the change to all of its predecessors.  In
 * order to detect and break cycles, we mark a node busy by changing the
 * last byte of its name buffer (which should be 0) while iterating over
 * its children, then change it back when we are done.
 */
static void
pnode_raise(pnode *n, unsigned long prio)
{
	aa_iterator *nit;
	pnode *p;

	if (n->prio >= prio)
		return;
	verbose("raising the priority of node %s from %lu to %lu",
	    n->name, n->prio, prio);
	n->prio = prio;
	n->name[NAMELEN] = '*';
	for (p = aa_first(&n->pred, &nit); p != NULL; p = aa_next(&nit)) {
		if (p->name[NAMELEN] != '\0') {
			if (!quiet)
				warnx("cycle involving %.*s and %.*s",
				    NAMELEN, p->name, NAMELEN, n->name);
			if (strict)
				exit(3);
			continue;
		}
		pnode_raise(p, n->prio + 1);
	}
	aa_finish(&nit);
	n->name[NAMELEN] = '\0';
}

/*
 * Read nodes and edges from a file and construct our graph, setting and
 * propagating node priorities as we go along.
 *
 * Each line is either:
 *
 * PREDNODE SUCCNODE
 *    Insert an edge from PREDNODE to SUCCNODE
 *
 * NODE NUMBER
 *    Raise NODE's priority to NUMBER if not already higher
 *
 * NODE NODE
 *    Insert NODE if it doesn't already exist
 *
 * Node names are arbitrary sequences of up to 255 ASCII printable,
 * non-whitespace characters.  However, it is not safe to give a node a
 * name consisting entirely of digits, as it may be interpreted as a
 * priority.
 *
 * We keep nodes in a sorted balanced search tree for easy lookup and
 * deduplication.  Each node contains a NUL-terminated name (which is also
 * the sorting key), a sorted balanced search tree of its predecessors and
 * a priority.  When traversing the graph to propagate priorities, the
 * last byte of the name is used as a processing mark for loop detection.
 *
 * We keep a node in reserve so we don't have to keep allocating new nodes
 * and then freeing them when they turn out to already be in the tree.
 * This way, we only allocate a new node when we've consumed the one we
 * had on hand.
 */
static void
input(const char *fn)
{
	FILE *f;
	struct pnode *pn, *sn, *rn; /* pred / succ / reserve node */
	struct pnode *n;
	const char *pnb, *pne, *snb, *sne; /* pred / succ name beg / end */
	const char *line, *p;
	char *e;
	unsigned long nlines, nedges, nnodes;
	unsigned long prio;

	/* open input file */
	if (fn == NULL || strcmp(fn, "-") == 0) {
		fn = "stdin";
		f = stdin;
	} else if ((f = fopen(fn, "r")) == NULL) {
		err(1, "%s", fn);
	}

	/* allocate our reserve node */
	rn = pnode_new();

	/* read line by line */
	nlines = nedges = nnodes = 0;
	while ((line = freadline(f)) != NULL) {
		nlines++;
		/* leading whitespace */
		for (p = line; is_space(*p); p++)
			/* nothing */;
		/* name of predecessor */
		for (pnb = p; is_name(*p); p++)
			/* nothing */;
		/* separating whitespace */
		for (pne = p; is_space(*p); p++)
			/* nothing */;
		/* name of successor *or* numeric priority */
		for (snb = p; is_name(*p); p++)
			/* nothing */;
		/* trailing whitespace */
		for (sne = p; is_space(*p); p++)
			/* nothing */;
		/* terminating newline */
		if (*p == '\n')
			p++;
		/* check lengths */
		if (pne - pnb == 0 || pne - pnb > NAMELEN ||
		    sne - snb == 0 || sne - pnb > NAMELEN ||
		    *p != '\0') {
			errx(2, "%s:%lu: syntax error:\n%s", fn, nlines, line);
			continue;
		}
		/* prepare predecessor node */
		strncpy(rn->name, pnb, pne - pnb);
		if ((pn = aa_insert(&nodes, rn)) == NULL)
			err(1, "aa_insert()");
		if (pn == rn) {
			/* new node */
			verbose("insert new node %s", pn->name);
			rn = pnode_new();
			nnodes++;
		} else {
			/* clear reserve for reuse */
			memset(rn->name, 0, sizeof rn->name);
		}
		/* successor or priority */
		prio = strtoul(snb, &e, 10);
		if (e == sne) {
			/* raise this node's priority */
			pnode_raise(pn, prio);
		} else if (pne - pnb == sne - snb &&
		    strncmp(pnb, snb, pne - pnb) == 0) {
			/* no-op for compatibility with tsort */
			continue;
		} else {
			/* prepare successor node */
			strncpy(rn->name, snb, sne - snb);
			if ((sn = aa_insert(&nodes, rn)) == NULL)
				err(1, "aa_insert()");
			if (sn == rn) {
				/* new node */
				verbose("insert new node %s", sn->name);
				rn = pnode_new();
				nnodes++;
			} else {
				/* clear reserve for reuse */
				memset(rn->name, 0, sizeof rn->name);
			}
			/* create the edge between predecessor and successor */
			if ((n = aa_insert(&sn->pred, pn)) == NULL)
				err(1, "aa_insert()");
			if (n == pn) {
				/* new edge */
				verbose("insert new edge from %s to %s",
				    pn->name, sn->name);
				nedges++;
				pnode_raise(pn, sn->prio + 1);
			}
		}
	}
	if (ferror(f))
		err(1, "%s", fn);
	if (f != stdin)
		fclose(f);
	free(rn);
	verbose("read %lu lines from %s", nlines, fn);
	verbose("inserted %lu new nodes and %lu new edges", nnodes, nedges);
	tnedges += nedges;
	tnnodes += nnodes;
}

/*
 * Output a partial ordering of the nodes in the graph.  We form an array
 * of pointers to all of our notes, sort them by priority and print the
 * names in reverse order.
 */
static void
output(const char *fn)
{
	aa_iterator *nit;
	pnode **all, **p;
	pnode *n;
	FILE *f;

	/* allocate array of pointers */
	if ((p = all = malloc(tnnodes * sizeof *all)) == NULL)
		err(1, "malloc()");

	/* copy nodes into array in lexical order */
	for (n = aa_first(&nodes, &nit); n != NULL; n = aa_next(&nit))
		*p++ = n;
	aa_finish(&nit);
	/* p now points one past the end of the array */

	/* sort by priority */
	qsort(all, tnnodes, sizeof *all, pnodep_priocmp);

	/* output to file or stdout */
	if (fn == NULL)
		f = stdout;
	else if ((f = fopen(fn, "w")) == NULL)
		err(1, "%s", fn);

	/* reverse through the array and print each node's name */
	while (p-- > all) {
		if (printprio)
			fprintf(f, "%7lu ", (*p)->prio);
		fprintf(f, "%s\n", (*p)->name);
	}

	/* done */
	if (f != stdout)
		fclose(f);
}

static void
usage(void)
{

	fprintf(stderr, "usage: ptsort [-pqsv] [-o output] [input ...]\n");
	exit(1);
}

int
main(int argc, char *argv[])
{
	const char *ofn = NULL;
	int opt;

	aa_init(&nodes, (aa_comparator)strcmp);

	while ((opt = getopt(argc, argv, "opqsv")) != -1)
		switch (opt) {
		case 'o':
			ofn = optarg;
			break;
		case 'p':
			printprio = 1;
			break;
		case 'q':
			quiet = 1;
			break;
		case 's':
			strict = 1;
			break;
		case 'v':
			vlevel++;
			break;
		default:
			usage();
		}

	argc -= optind;
	argv += optind;

	if (argc == 0)
		input(NULL);
	else
		while (argc--)
			input(*argv++);
	verbose("graph has %lu nodes and %lu edges", tnnodes, tnedges);
	output(ofn);
	exit(0);
}
