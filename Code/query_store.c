// query.c ... query scan functions
// part of Multi-attribute Linear-hashed Files
// Manage creating and using Query objects
// Last modified by John Shepherd, July 2019

#include "defs.h"
#include "query.h"
#include "reln.h"
#include "tuple.h"
#include "bits.h"
#include "hash.h"

// A suggestion ... you can change however you like
#define INT_SIZE sizeof(int) * 8

struct QueryRep {
	Reln    rel;       // need to remember Relation info
	//char    *known;     // the hash value from MAH
	//char    *unknown;   // the unknown bits from MAH
	PageID  curpage;   // current page in scan
	int     is_ovflow; // are we in the overflow pages?
	Offset  curtup;    // offset of current tuple within page
	char 	*querystring;
	int     *pages;
	int     page_num;
	//TODO
};

// take a query string (e.g. "1234,?,abc,?")
// set up a QueryRep object for the scan
void bitwise_char(Bits src,char *pid_bits){
	for(int kk = sizeof(unsigned int) * 8 - 1; kk >= 0; --kk){
		pid_bits[MAXBITS-kk-1] = src >> kk & 1;
	}
}

unsigned int bitwise_get(Bits src, int src_bit) {
	return ((src >> (sizeof(Bits) * 8 - 1 - src_bit)) & 1);
}

int reverseBits(int n)
{
    int pos = INT_SIZE - 1;     // maintains shift
 
    // store reversed bits of `n`. Initially, all bits are set to 0
    int reverse = 0;
 
    // do till all bits are processed
    while (pos >= 0 && n)
    {
        // if the current bit is 1, then set the corresponding bit in the result
        if (n & 1) {
            reverse = reverse | (1 << pos);
        }
 
        n >>= 1;                // drop current bit (divide by 2)
        pos--;                  // decrement shift by 1
    }
 
    return reverse;
}

Query startQuery(Reln r, char *q)
{
	//printf("startQuery 0\n");
	Query new = malloc(sizeof(struct QueryRep));
	assert(new != NULL);
	Count nvals = nattrs(r);
	Bits hashval[nvals];
	ChVecItem *choiceVector = chvec(r);
	char **vals = malloc(nvals*sizeof(char *));
	tupleVals(q,vals);
	char* known = calloc(MAXBITS, sizeof(char));
	char* unknown = calloc(MAXBITS, sizeof(char));
	//printf("startQuery 1\n");
	//int* pages = calloc(npages(r), sizeof(int));
	int* pages2 = calloc(npages(r), sizeof(int));
	for (int i = 0; i < MAXBITS; i++) {
		int att_value = choiceVector[i].att;
		if (strcmp(vals[att_value], "?") == 0) {
			unknown[i] = 1;
		} else {
			hashval[att_value] = hash_any((unsigned char *)vals[att_value],strlen(vals[att_value]));
			known[i] = bitIsSet(hashval[att_value], choiceVector[i].bit);
		}
	}
	/*
	for (int i = 0; i < depth(r); i++) {
		printf(" known(%d) \n", known[i]);
	}
	for (int i = 0; i < depth(r); i++) {
		printf(" unknown(%d) \n", unknown[i]);
	}*/
	/*
	for (int i = 0; i < nvals; i++) {
		if (strcmp(vals[i],"?")==0) {
			for (int j=0;j < MAXBITS;j++) {
				if (i == choiceVector[j].att) {
					unknown[MAXBITS-j-1] = 1;
				}
			}
		} else {
			hashval[i] = hash_any((unsigned char *)vals[i],strlen(vals[i]));
			for (int j=0;j < MAXBITS;j++) {
				if (i == choiceVector[j].att) {
					known[MAXBITS-j-1] = bitIsSet(hashval[i], choiceVector[j].bit);
					//known[MAXBITS-j-1] = bitwise_get(hashval[i],MAXBITS-choiceVector[j].bit-1);
				}
			}
		}
	}*/
	//int result = 0;
	int bit = 1;
	int page_record = 1;
	pages2[0] = 0;
	//printf("startQuery 2\n");
	//printf("depth: %d\n", depth(r));
	for (int j = 0;j <= depth(r);j++) {
		if (j == depth(r)) {
			for (int i = 0; i < page_record; i++) {
				if (pages2[i] < splitp(r)) {
					if (known[depth(r)] == 1) {
						pages2[i] = pages2[i] | (1 << depth(r));
					}
					if (unknown[depth(r)] == 1) {
						pages2[page_record+1] = pages2[i] | (1 << depth(r));
						page_record++;
					}
				}
			}
		} else {
			for (int k = 0; k < page_record; k++) {
				pages2[k] = pages2[k] << 1;
			}
			if (known[depth(r)-j-1] == 1) {
				for (int k = 0; k < page_record; k++) {
					pages2[k] = pages2[k] | bit;
				}
			}
			if (unknown[depth(r)-j-1] == 1) {
				for (int k = 0; k < page_record; k++) {
					pages2[page_record+k] = pages2[k] | bit;
				}
				
				page_record = 2*page_record;
				
			}
		}
	}
	/*
	for (int i = 0; i < page_record; i++) {
		printf(" page_id(%d) \n", pages2[i]);
	}
	
	for (int i = 0; i < page_record; i++) {
		pages2[i] = pages2[i];
	}*/
	
	//printf("startQuery 3\n");
	
	/*
	page_record = 0;
	char buf[MAXBITS];
	for (int page_id = 0; page_id < npages(r); page_id++) {
		bitwise_char(page_id, buf);
		Bool judge = TRUE;
		if (page_id >= splitp(r)) {
			for (int i = MAXBITS-depth(r);i<MAXBITS;i++) {
				if (known[i] == 3) {
					continue;
				} else if (buf[i] != known[i]) {
					judge = FALSE;
					break;
				}
			}
		} else {
			for (int i = MAXBITS-depth(r)-1;i<MAXBITS;i++) {
				if (known[i] == 3) {
					continue;
				} else if (buf[i] != known[i]) {
					judge = FALSE;
					break;
				}
			}
		}
		if (judge == TRUE) {
			pages[page_record] = page_id;
			page_record++;
		} 
	}*/
	//printf("startQuery 3\n");
	/*
	for (int i = 0; i < page_record; i++) {
		printf(" page_id(%d) \n", pages2[i]);
	}
	*/
	

	new -> rel = r;
	new -> is_ovflow = -1;
	new -> curpage = 0;
	new -> curtup = 0;
	new -> querystring = q;
	//new -> known = known;
	//new -> unknown = unknown;
	new -> pages = pages2;
	new -> page_num = page_record;
	// TODO
	// Partial algorithm:
	// form known bits from known attributes
	// form unknown bits from '?' attributes
	// compute PageID of first page
	//   using known bits and first "unknown" value
	// set all values in QueryRep object
	return new;
}

// get next tuple during a scan

Tuple getNextTuple(Query q)
{
	// TODO
	// Partial algorithm:
	// if (more tuples in current page)
	//    get next matching tuple from current page
	// else if (current page has overflow)
	//    move to overflow page
	//    grab first matching tuple from page
	// else
	//    move to "next" bucket
	//    grab first matching tuple from data page
	// endif
	// if (current page has no matching tuples)
	//    go to next page (try again)
	// endif
	
	//Reln rel = q -> rel;
	//char *query = q -> querystring;
	//char *known = new -> known;
	//char *unknown = new -> unknown;
	int *pages = q->pages;

	
	for (int i = 0; i < npages(q->rel); i++) {
		printf(" page_id(%d) \n", pages[i]);
	}
	//printf("start\n");
	for (int i = q->curpage; i < q->page_num; i++) {
		Count size = 2*sizeof(Offset) + sizeof(Count);
		int dataSize = PAGESIZE - size;
		//printf("page id: %d \n", pages[i]);
		if (q->is_ovflow == -1) {
			//printf("No overflow\n");
			Page p = getPage(dataFile(q->rel),pages[i]);
			char *data = pageData(p);
			int count = q->curtup;
			for(int h=q->curtup;h < dataSize;h++){
				//printf("loop for rurtup\n");
				if(data[h] == '\0'){
					if(h == count){
						break;
					}
					if(tupleMatch(q->rel,&data[count],q->querystring) == TRUE){
						q->curpage = i;
						q->curtup = h+1;
						free(p);
						//printf("end 0\n");
						return &data[count];
					}
					else {
						count = h+1;
					}
				}
			}
			if(pageOvflow(p)!= -1){
				q->is_ovflow = pageOvflow(p);
				q->curtup = 0;
			}
			else{
				q->curpage = i+1;
				q->curtup = 0;
			}
			free(p);
		}
		if(q->is_ovflow != -1) {
			//printf("overflow\n");
			while(q->is_ovflow != -1){
				//printf(" overflow:%d ",q->is_ovflow);
				int count = q->curtup;
				Page p = getPage(ovflowFile(q->rel), q->is_ovflow);
				char *data = pageData(p);
				for(int h=q->curtup;h < dataSize;h++){
					if(data[h] == '\0'){
						if(h == count){
							break;
						}
						if(tupleMatch(q->rel,&data[count],q->querystring) == TRUE) {
							q->curtup = h+1;
							free(p);
							//printf("end 1\n");
							return &data[count];
						}
						else{
							count = h+1;
						}
					}
				}
				if (pageOvflow(p)!= -1) {
					q->is_ovflow = pageOvflow(p);
					q->curtup = 0;
				}else{
					q->is_ovflow = -1;
					q->curtup = 0;
					q->curpage = i+1;
				}
				free(p);
			}
		}
	}
	//printf("end\n");
	return NULL;
}

void closeQuery(Query q)
{
	free(q);
}

	/*
	char buf[MAXBITS];
	for (int npage = q -> curpage; npage < npages(r); npage++) {
		bitsString(npage, buf);
		if (npage > rel->sp) {

		}
	}*/

	//    get next matching tuple from current page
	// else if (current page has overflow)
	//    move to overflow page
	//    grab first matching tuple from page
	// else
	//    move to "next" bucket
	//    grab first matching tuple from data page
	// endif
	// if (current page has no matching tuples)
	//    go to next page (try again)
	// endif


// clean up a QueryRep object and associated data