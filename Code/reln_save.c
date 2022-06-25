// reln.c ... functions on Relations
// part of Multi-attribute Linear-hashed Files
// Last modified by John Shepherd, July 2019

#include "defs.h"
#include "reln.h"
#include "page.h"
#include "tuple.h"
#include "chvec.h"
#include "bits.h"
#include "hash.h"

#define HEADERSIZE (3*sizeof(Count)+sizeof(Offset))

struct RelnRep {
	Count  nattrs; // number of attributes
	Count  depth;  // depth of main data file
	Offset sp;     // split pointer
    Count  npages; // number of main data pages
    Count  ntups;  // total number of tuples
	ChVec  cv;     // choice vector
	char   mode;   // open for read/write
	FILE  *info;   // handle on info file
	FILE  *data;   // handle on data file
	FILE  *ovflow; // handle on ovflow file
	int insertionNumber; //Record intersion number
};

// create a new relation (three files)

Status newRelation(char *name, Count nattrs, Count npages, Count d, char *cv)
{
    char fname[MAXFILENAME];
	Reln r = malloc(sizeof(struct RelnRep));
	r->nattrs = nattrs; r->depth = d; r->sp = 0;
	r->npages = npages; r->ntups = 0; r->mode = 'w';
	assert(r != NULL);
	if (parseChVec(r, cv, r->cv) != OK) return ~OK;
	sprintf(fname,"%s.info",name);
	r->info = fopen(fname,"w");
	assert(r->info != NULL);
	sprintf(fname,"%s.data",name);
	r->data = fopen(fname,"w");
	assert(r->data != NULL);
	sprintf(fname,"%s.ovflow",name);
	r->ovflow = fopen(fname,"w");
	assert(r->ovflow != NULL);
	int i;
	for (i = 0; i < npages; i++) addPage(r->data);
	closeRelation(r);
	return 0;
}

// check whether a relation already exists

Bool existsRelation(char *name)
{
	char fname[MAXFILENAME];
	sprintf(fname,"%s.info",name);
	FILE *f = fopen(fname,"r");
	if (f == NULL)
		return FALSE;
	else {
		fclose(f);
		return TRUE;
	}
}

// set up a relation descriptor from relation name
// open files, reads information from rel.info

Reln openRelation(char *name, char *mode)
{
	Reln r;
	r = malloc(sizeof(struct RelnRep));
	assert(r != NULL);
	char fname[MAXFILENAME];
	sprintf(fname,"%s.info",name);
	r->info = fopen(fname,mode);
	assert(r->info != NULL);
	sprintf(fname,"%s.data",name);
	r->data = fopen(fname,mode);
	assert(r->data != NULL);
	sprintf(fname,"%s.ovflow",name);
	r->ovflow = fopen(fname,mode);
	assert(r->ovflow != NULL);
	// Naughty: assumes Count and Offset are the same size
	int n = fread(r, sizeof(Count), 5, r->info);
	assert(n == 5);
	n = fread(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
	assert(n == MAXCHVEC);
	r->mode = (mode[0] == 'w' || mode[1] =='+') ? 'w' : 'r';
	return r;
}

// release files and descriptor for an open relation
// copy latest information to .info file

void closeRelation(Reln r)
{
	// make sure updated global data is put in info
	// Naughty: assumes Count and Offset are the same size
	if (r->mode == 'w') {
		fseek(r->info, 0, SEEK_SET);
		// write out core relation info (#attr,#pages,d,sp)
		int n = fwrite(r, sizeof(Count), 5, r->info);
		assert(n == 5);
		// write out choice vector
		n = fwrite(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
		assert(n == MAXCHVEC);
	}
	fclose(r->info);
	fclose(r->data);
	fclose(r->ovflow);
	free(r);
}

// insert a new tuple into a relation
// returns index of bucket where inserted
// - index always refers to a primary data page
// - the actual insertion page may be either a data page or an overflow page
// returns NO_PAGE if insert fails completely
// TODO: include splitting and file expansion
static double power(double a, int b) {
	int r = 1;
	for(int i = 0; i < b; ++i) {
		r *= a;
	}
	return r;
}

PageID addToRelation(Reln r, Tuple t)
{
	/*
	for all tuples t in P[oldp] and its overflows {
		p = bits(d+1,hash(t.k));
		if (p == newp) 
			add tuple t to bucket[newp]
		else
			add tuple t to bucket[oldp]
	}*/

	int capcity = 1024 / (10 * (r->nattrs));
	Offset newp = r->sp + power(2, (r->depth)); 
	Offset oldp = r->sp;

	Bits h, p;
	h = tupleHash(r,t);
	if ((r->insertionNumber) >= capcity)
	{
		// Get data from old page
		Page pg = getPage(dataFile(r), oldp);
		char *data = pageData(pg);
		Offset ovg = pageOvflow(pg);

		// Create the first new page with old id
		Page np1 = newPage();
		pageSetOvflow(np1, ovg);
		putPage(r->data, oldp, np1);
		np1 = getPage(dataFile(r), oldp);

		// Create the second new page with new id
		Page np2 = newPage();
		putPage(r->data, newp, np2);
		np2 = getPage(dataFile(r), newp);

		while (strlen(data) != 0)
		{	
			int l = strlen(data);
			h = tupleHash(r, data);
			p = getLower(h, r->depth + 1);
			if (p == oldp)
			{
				if (addToPage(np1, &data[0]) == OK)
				{
					putPage(r->data, p, np1);
					np1 = getPage(r->data, p);
				} else {
					if (pageOvflow(np1) == NO_PAGE) {
						// add first overflow page in chain
						PageID newp = addPage(r->ovflow);
						pageSetOvflow(np1,newp);
						putPage(r->data,p,np1);
						Page newpg = getPage(r->ovflow,newp);
						// can't add to a new page; we have a problem
						if (addToPage(newpg,t) != OK) return NO_PAGE;
						putPage(r->ovflow,newp,newpg);
						
					} else {
						// scan overflow chain until we find space
						// worst case: 
						Page ovpg, prevpg = NULL;
						PageID ovp = NO_PAGE;
						ovp = pageOvflow(np1);
						while (ovp != NO_PAGE) {
							ovpg = getPage(r->ovflow, ovp);
							if (addToPage(ovpg,t) != OK) {
								prevpg = ovpg;
								ovp = pageOvflow(ovpg);
							}
							else {
								if (prevpg != NULL) free(prevpg);
								putPage(r->ovflow,ovp,ovpg);
								break;
							}
						}
					}
				}
			}
			else
			{
				if (addToPage(np2, &data[0]) == OK)
				{
					putPage(r->data, p, np2);
					np2 = getPage(r->data, p);
				} else {
					if (pageOvflow(np1) == NO_PAGE) {
						// add first overflow page in chain
						PageID newp = addPage(r->ovflow);
						pageSetOvflow(np1,newp);
						putPage(r->data,p,np1);
						Page newpg = getPage(r->ovflow,newp);
						// can't add to a new page; we have a problem
						if (addToPage(newpg,t) != OK) return NO_PAGE;
						putPage(r->ovflow,newp,newpg);
						
						
					} else {
						// scan overflow chain until we find space
						// worst case: 
						Page ovpg, prevpg = NULL;
						PageID ovp = NO_PAGE;
						ovp = pageOvflow(np1);
						while (ovp != NO_PAGE) {
							ovpg = getPage(r->ovflow, ovp);
							if (addToPage(ovpg,t) != OK) {
								prevpg = ovpg;
								ovp = pageOvflow(ovpg);
							}
							else {
								if (prevpg != NULL) free(prevpg);
								putPage(r->ovflow,ovp,ovpg);
								break;
							}
						}
					}
				}
			}
			data += l + 1;
		}
		Page prep1 = np1;
		Page prep2 = np2;
		FILE *current_d = r->data;
		FILE *(*dfp)(Reln);
		dfp = &dataFile;
		FILE *current_d2 = r->data;
		FILE *(*dfp2)(Reln);
		dfp2 = &dataFile;	
		while (ovg != NO_PAGE)
		{
			Page ovg_pg = getPage(ovflowFile(r), ovg);
			Offset xx = pageOvflow(ovg_pg);
			char *current_c = pageData(ovg_pg);
			Page ovppn = newPage();
			pageSetOvflow(ovppn, xx);
			putPage(r->ovflow, ovg, ovppn);
			while (strlen(current_c) != 0)
			{
				int l = strlen(current_c);
				h = tupleHash(r, current_c);
				p = getLower(h, r->depth + 1);
				if (p == r->sp)
				{
					prep1 = getPage((*dfp)(r), p);
					while (addToPage(prep1, &current_c[0]) != OK)
					{
						p = pageOvflow(prep1);
						current_d = r->ovflow;
						dfp = &ovflowFile;
						prep1 = getPage((*dfp)(r), p);
					}
					putPage(current_d, p, prep1);
				}
				else
				{
					prep2 = getPage((*dfp2)(r), p);
					while (addToPage(prep2, &current_c[0]) != OK)
					{
						current_d2 = r->ovflow;
						dfp2 = &ovflowFile;
						p = pageOvflow(prep2);
						if (p == NO_PAGE) {
							PageID newp = addPage(r->ovflow);
							pageSetOvflow(prep2, newp);
							putPage(r->data, p, prep2);
							prep2 = getPage((*dfp2)(r), p);
							p = pageOvflow(prep2);
						}
						prep2 = getPage((*dfp2)(r), p);
					}
					putPage(current_d2, p, prep2);
				}
				current_c += l + 1;
			}

			ovg = pageOvflow(ovg_pg);
		}

		r->insertionNumber = 0;
		r->sp ++;
		r->npages ++;
		if (r->sp == power(2, (r->depth+1))) { r->depth++; r->sp = 0; }
	}
	// char buf[MAXBITS+1];
	h = tupleHash(r,t);
	if (r->depth == 0)
		p = 0;
	else {
		p = getLower(h, r->depth);
		if (p < r->sp) p = getLower(h, r->depth+1);
	}
	// bitsString(h,buf); printf("hash = %s\n",buf);
	// bitsString(p,buf); printf("page = %s\n",buf);
	Page pg = getPage(r->data,p);
	if (addToPage(pg,t) == OK) {
		putPage(r->data,p,pg);
		r->ntups++;
		r->insertionNumber++;
		return p;
	}
	// primary data page full
	if (pageOvflow(pg) == NO_PAGE) {
		// add first overflow page in chain
		PageID newp = addPage(r->ovflow);
		pageSetOvflow(pg,newp);
		putPage(r->data,p,pg);
		Page newpg = getPage(r->ovflow,newp);
		// can't add to a new page; we have a problem
		if (addToPage(newpg,t) != OK) return NO_PAGE;
		putPage(r->ovflow,newp,newpg);
		r->ntups++;
		r->insertionNumber++;
		return p;
	}
	else {
		// scan overflow chain until we find space
		// worst case: add new ovflow page at end of chain
		Page ovpg, prevpg = NULL;
		PageID ovp, prevp = NO_PAGE;
		ovp = pageOvflow(pg);
		while (ovp != NO_PAGE) {
			ovpg = getPage(r->ovflow, ovp);
			if (addToPage(ovpg,t) != OK) {
				prevp = ovp; prevpg = ovpg;
				ovp = pageOvflow(ovpg);
			}
			else {
				if (prevpg != NULL) free(prevpg);
				putPage(r->ovflow,ovp,ovpg);
				r->ntups++;
				r->insertionNumber++;
				return p;
			}
		}
		// all overflow pages are full; add another to chain
		// at this point, there *must* be a prevpg
		assert(prevpg != NULL);
		// make new ovflow page
		PageID newp = addPage(r->ovflow);
		// insert tuple into new page
		Page newpg = getPage(r->ovflow,newp);
        if (addToPage(newpg,t) != OK) return NO_PAGE;
        putPage(r->ovflow,newp,newpg);
		// link to existing overflow chain
		pageSetOvflow(prevpg,newp);
		putPage(r->ovflow,prevp,prevpg);
        r->ntups++;
		r->insertionNumber++;
		return p;
	}
	return NO_PAGE;
}

// external interfaces for Reln data

FILE *dataFile(Reln r) { return r->data; }
FILE *ovflowFile(Reln r) { return r->ovflow; }
Count nattrs(Reln r) { return r->nattrs; }
Count npages(Reln r) { return r->npages; }
Count ntuples(Reln r) { return r->ntups; }
Count depth(Reln r)  { return r->depth; }
Count splitp(Reln r) { return r->sp; }
ChVecItem *chvec(Reln r)  { return r->cv; }


// displays info about open Reln

void relationStats(Reln r)
{
	printf("Global Info:\n");
	printf("#attrs:%d  #pages:%d  #tuples:%d  d:%d  sp:%d\n",
	       r->nattrs, r->npages, r->ntups, r->depth, r->sp);
	printf("Choice vector\n");
	printChVec(r->cv);
	printf("Bucket Info:\n");
	printf("%-4s %s\n","#","Info on pages in bucket");
	printf("%-4s %s\n","","(pageID,#tuples,freebytes,ovflow)");
	for (Offset pid = 0; pid < r->npages; pid++) {
		printf("[%2d]  ",pid);
		Page p = getPage(r->data, pid);
		Count ntups = pageNTuples(p);
		Count space = pageFreeSpace(p);
		Offset ovid = pageOvflow(p);
		printf("(d%d,%d,%d,%d)",pid,ntups,space,ovid);
		free(p);
		while (ovid != NO_PAGE) {
			Offset curid = ovid;
			p = getPage(r->ovflow, ovid);
			ntups = pageNTuples(p);
			space = pageFreeSpace(p);
			ovid = pageOvflow(p);
			printf(" -> (ov%d,%d,%d,%d)",curid,ntups,space,ovid);
			free(p);
		}
		putchar('\n');
	}
}
