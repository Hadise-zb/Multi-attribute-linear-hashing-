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

PageID addToRelation(Reln r, Tuple t)
{
	//printf("addToRelation 0\n");
	

	int capcity = 1024 / (10 * (r->nattrs));

	Bits h, p;
	if (((r->ntups + 1)% capcity) == 0)
	{
		// Get data from old page
		//printf("addToRelation 1\n");
		Offset newp = r->sp + (int)(1 << r->depth);
		Offset oldp = r->sp;
		
		Page pg = getPage(dataFile(r), oldp);
		
		char *data = pageData(pg);
		Offset ovg = pageOvflow(pg);

		// Create the first new page with old id
		Page NewPage1 = newPage();
		pageSetOvflow(NewPage1, ovg);
		putPage(r->data, oldp, NewPage1);
		NewPage1 = getPage(dataFile(r), oldp);

		// Create the second new page with new id
		Page NewPage2 = newPage();
		putPage(r->data, newp, NewPage2);
		NewPage2 = getPage(dataFile(r), newp);

		while (strlen(data) != 0)
		{	
			int tuple_length = strlen(data);
			h = tupleHash(r, data);
			p = getLower(h, r->depth + 1);

			if (p == r->sp)
			{
				if (addToPage(NewPage1, &data[0]) == OK)
				{
					putPage(r->data, p, NewPage1);
					NewPage1 = getPage(r->data, p);
				}
				else
				{
					if (pageOvflow(NewPage1) == NO_PAGE) {
						// add first overflow page in chain
						PageID newp = addPage(r->ovflow);
						pageSetOvflow(NewPage1,newp);
						putPage(r->data,p,NewPage1);
						Page newpg = getPage(r->ovflow,newp);
						// can't add to a new page; we have a problem
						if (addToPage(newpg,&data[0]) != OK) return NO_PAGE;
						putPage(r->ovflow,newp,newpg);
						
					} else {
						// scan overflow chain until we find space
						Page ovpg, prevpg = NULL;
						PageID ovp, prevp = NO_PAGE;
						ovp = pageOvflow(NewPage1);
						while (ovp != NO_PAGE) {
							ovpg = getPage(r->ovflow, ovp);
							if (addToPage(ovpg,&data[0]) != OK) {
								prevp = ovp;
								prevpg = ovpg;
								ovp = pageOvflow(ovpg);
							}
							else {
								if (prevpg != NULL) free(prevpg);
								putPage(r->ovflow,ovp,ovpg);
								break;
							}
						}
						// all overflow pages are full; add another to chain
						// at this point, there *must* be a prevpg
						assert(prevpg != NULL);
						// make new ovflow page
						PageID newp = addPage(r->ovflow);
						// insert tuple into new page
						Page newpg = getPage(r->ovflow,newp);
						if (addToPage(newpg,&data[0]) != OK) return NO_PAGE;
						putPage(r->ovflow,newp,newpg);
						// link to existing overflow chain
						pageSetOvflow(prevpg,newp);
						putPage(r->ovflow,prevp,prevpg);

					}
				}
			}
			else
			{
				if (addToPage(NewPage2, &data[0]) == OK)
				{
					putPage(r->data, p, NewPage2);
					//printf("addToRelation 7\n");
					NewPage2 = getPage(r->data, p);
				}
				else
				{
					if (pageOvflow(NewPage1) == NO_PAGE) {
						// add first overflow page in chain
						PageID newp = addPage(r->ovflow);
						pageSetOvflow(NewPage1,newp);
						putPage(r->data,p,NewPage1);
						//printf("addToRelation 8\n");
						Page newpg = getPage(r->ovflow,newp);
						// can't add to a new page; we have a problem
						if (addToPage(newpg,&data[0]) != OK) return NO_PAGE;
						putPage(r->ovflow,newp,newpg);
						
						
					} else {
						// scan overflow chain until we find space
						// worst case: 
						Page ovpg, prevpg = NULL;
						PageID ovp, prevp = NO_PAGE;
						ovp = pageOvflow(NewPage1);
						while (ovp != NO_PAGE) {
							//printf("addToRelation 9\n");
							ovpg = getPage(r->ovflow, ovp);
							if (addToPage(ovpg,&data[0]) != OK) {
								prevp = ovp;
								prevpg = ovpg;
								ovp = pageOvflow(ovpg);
							}
							else {
								if (prevpg != NULL) free(prevpg);
								putPage(r->ovflow,ovp,ovpg);
								break;
							}
						}

						// all overflow pages are full; add another to chain
						// at this point, there *must* be a prevpg
						assert(prevpg != NULL);
						// make new ovflow page
						PageID newp = addPage(r->ovflow);
						// insert tuple into new page
						Page newpg = getPage(r->ovflow,newp);
						if (addToPage(newpg,&data[0]) != OK) return NO_PAGE;
						putPage(r->ovflow,newp,newpg);
						// link to existing overflow chain
						pageSetOvflow(prevpg,newp);
						putPage(r->ovflow,prevp,prevpg);
					}
				}
			}
			data = data + tuple_length + 1;
		}
		
		while (ovg != NO_PAGE)
		{
			Page ovg_pg = getPage(ovflowFile(r), ovg);
			Offset overflowpage = pageOvflow(ovg_pg);
			char *data = pageData(ovg_pg);
			Page ovppn = newPage();
			pageSetOvflow(ovppn, overflowpage);
			putPage(r->ovflow, ovg, ovppn);
			while (strlen(data) != 0)
			{
				int tuple_length = strlen(data);
				h = tupleHash(r, data);
				p = getLower(h, r->depth + 1);
				if (p == r->sp)
				{
					//printf("addToRelation 11\n");
					NewPage1 = getPage(r->data, p);
					int judge = 0;
					if (addToPage(NewPage1, &data[0]) == OK) {
						putPage(r->data, p, NewPage1);
						NewPage1 = getPage(r->data, p);
						judge = 1;
					} else {
						
						if (pageOvflow(NewPage1) == NO_PAGE) {
							// add first overflow page in chain
							PageID newp = addPage(r->ovflow);
							pageSetOvflow(NewPage1,newp);
							putPage(r->data,p,NewPage1);
							//printf("addToRelation 5\n");
							Page newpg = getPage(r->ovflow,newp);
							// can't add to a new page; we have a problem
							if (addToPage(newpg,&data[0]) != OK) return NO_PAGE;
							putPage(r->ovflow,newp,newpg);
							judge = 1;
						} else {
							// scan overflow chain until we find space
							Page ovpg, prevpg = NULL;
							PageID ovp, prevp = NO_PAGE;
							ovp = pageOvflow(NewPage1);
							while (ovp != NO_PAGE) {
								//printf("addToRelation 6\n");
								ovpg = getPage(r->ovflow, ovp);
								if (addToPage(ovpg,&data[0]) != OK) {
									prevp = ovp;
									prevpg = ovpg;
									ovp = pageOvflow(ovpg);
								}
								else {
									if (prevpg != NULL) free(prevpg);
									putPage(r->ovflow,ovp,ovpg);
									judge = 1;
									break;
								}
							}
							if (judge == 0) {
								// all overflow pages are full; add another to chain
								// at this point, there *must* be a prevpg
								assert(prevpg != NULL);
								// make new ovflow page
								PageID newp = addPage(r->ovflow);
								// insert tuple into new page
								Page newpg = getPage(r->ovflow,newp);
								if (addToPage(newpg,&data[0]) != OK) return NO_PAGE;
								putPage(r->ovflow,newp,newpg);
								// link to existing overflow chain
								pageSetOvflow(prevpg,newp);
								putPage(r->ovflow,prevp,prevpg);

								free(ovpg);
								judge = 1;
							}

						}
					}

				}
				else
				{
					NewPage2 = getPage(r->data, p);
					int judge = 0;
					if (addToPage(NewPage2, &data[0]) == OK) {
						putPage(r->data, p, NewPage2);
						NewPage2 = getPage(r->data, p);
						judge = 1;
					} else {
						if (pageOvflow(NewPage2) == NO_PAGE) {
							// add first overflow page in chain
							PageID newp = addPage(r->ovflow);
							pageSetOvflow(NewPage2,newp);
							putPage(r->data,p,NewPage2);
							//printf("addToRelation 5\n");
							Page newpg = getPage(r->ovflow,newp);
							// can't add to a new page; we have a problem
							if (addToPage(newpg,&data[0]) != OK) return NO_PAGE;
							putPage(r->ovflow,newp,newpg);
							judge = 1;
						} else {
							// scan overflow chain until we find space 
							Page ovpg, prevpg = NULL;
							PageID ovp, prevp = NO_PAGE;
							ovp = pageOvflow(NewPage2);
							while (ovp != NO_PAGE) {
								ovpg = getPage(r->ovflow, ovp);
								if (addToPage(ovpg,&data[0]) != OK) {
									prevp = ovp;
									prevpg = ovpg;
									ovp = pageOvflow(ovpg);
								}
								else {
									if (prevpg != NULL) free(prevpg);
									putPage(r->ovflow,ovp,ovpg);
									judge = 1;
									break;
								}
							}
							if (judge == 0) {
								// all overflow pages are full; add another to chain
								// at this point, there *must* be a prevpg
								assert(prevpg != NULL);
								// make new ovflow page
								PageID newp = addPage(r->ovflow);
								// insert tuple into new page
								Page newpg = getPage(r->ovflow,newp);
								if (addToPage(newpg,&data[0]) != OK) return NO_PAGE;
								putPage(r->ovflow,newp,newpg);
								// link to existing overflow chain
								pageSetOvflow(prevpg,newp);
								putPage(r->ovflow,prevp,prevpg);

								free(ovpg);
								judge = 1;
							}

						}
					}
					
				}
				data = data + tuple_length + 1;
			}
			ovg = pageOvflow(ovg_pg);
		}
		
		r->npages = r->npages + 1;
		r->sp = r->sp + 1;
		if (r->sp == (int)(1 << r->depth))
		{
			r->depth = r->depth + 1;
			r->sp = 0;
		}
	}

	//Bits h, p;
	// char buf[MAXBITS+1];
	h = tupleHash(r,t);
	if (r->depth == 0)
		p = 1;
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
