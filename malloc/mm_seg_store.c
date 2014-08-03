/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Nameless",
	/* First member's full name */
	"Eric Kang",
	/* First member's email address */
	"ek8@rice.edu",
	/* Second member's full name (leave blank if none) */
	"Jayson Carter",
	/* Second member's email address (leave blank if none) */
	"jjc7@rice.edu"
};


/* Basic constants and macros */
#define WSIZE           sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE           (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE       (1 << 12)      /* Extend heap by this amount (bytes) */
#define MINBLOCKSIZE    (5 * WSIZE)    /* Header, Footer, Data, Previous, Next */
#define NUMFREELISTS    (8)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)         (*(int *)(p))
#define PUT(p, val)    (*(int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)    (GET(p) & ~(WSIZE-1))
#define GET_ALLOC(p)   (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))

/* Returns the address of next and previous pointers */
#define GETNEXT(bp) ((char **)(bp + WSIZE))
#define GETPREV(bp) ((char **)(bp))

/* Allows you to set the pointers for next and prev */
#define SETNEXT(bp) ((*(char **)(bp + WSIZE)))
#define SETPREV(bp) ((*(char **)(bp)))

/* Global variables: */
static char *heap_listp;   /* Pointer to first block */
static char *free_listp;   /* Pointer to the beginning of free list */
static char *heap_arrayp;  /* Pointer to first block of array */
static int free_list_place;

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

static void addToBeginningOfFreeList(void *bp); 
static void removeBlockFromList(void *bp); 
static int log_2(unsigned int n);
static int placement(unsigned int n);


int 
mm_init(void) 
{
	//printf("IMA CHUGGIN");
	/* Create initial heap for other heaps */
	if ((heap_arrayp = mem_sbrk(NUMFREELISTS * sizeof(void **))) == (void *)-1)
		return (-1);

	/* Initialize page pointers to 0 */
	unsigned int index;
	for (index = 0; index < NUMFREELISTS; index++) {
		*(heap_arrayp + (index * WSIZE)) = 0;
		//printf("bing\n");
		//printf("bong\n");
	}
	return 0;
}


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
char *
mm_init2(void) 
{
	// WSIZE = 8 bytes            
	// DSIZE = 16 bytes             (2 * WSIZE)
	// MINBLOCKSIZE = 40 bytes      (5 * WSIZE)

      	/*  |P_Header|Prev_blockptr|Next_blockptr|Data_space|P_footer|E_header| */
	/*  8 bytes  8 bytes       8 bytes       8 bytes    8 bytes  8 bytes    */
	/*  |------------------MINBLOCKSIZE--------------------------|          */

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(MINBLOCKSIZE)) == (void *)-1) 
		return 0;
	PUT(heap_listp, PACK(MINBLOCKSIZE, 1));                /* Prologue header */ 
	PUT(heap_listp + (1 * WSIZE), 0);                      /* Pointer to PREV free block */
	PUT(heap_listp + (2 * WSIZE), 0);                      /* Pointer to NEXT free block */
	PUT(heap_listp + MINBLOCKSIZE, PACK(MINBLOCKSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + MINBLOCKSIZE + WSIZE, PACK(0, 1));    /* Epilogue header */
	/* NOTE: use 0 because null gives compile errors */

	free_listp = heap_listp + WSIZE;

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (0);
	
	return free_listp;
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;          /* Block Pointer */

	/* Ignore spurious requests. */
	if (size <= 0)
		return (NULL);
	
	/* Figure out which free list this block goes into */
	free_list_place = placement(log_2(size));

	if (*(char **)(heap_arrayp + free_list_place * WSIZE) == 0) {
		*(char **)(heap_arrayp + free_list_place * WSIZE) = mm_init2();
	}
	
	free_listp = *(char **)(heap_arrayp + free_list_place * WSIZE);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= WSIZE)
		asize = MINBLOCKSIZE;
	else
		asize = (2 * DSIZE) + WSIZE * ((size + (WSIZE - 1)) / WSIZE);   /* 32 + 8 * ((size + 7) / 8) */

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);

	//checkheap(true);
	//printblock(bp);
	//printf("bing\n");
	//	printf("bong\n");
	printf("malloc\n");
	checkheap(true);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void 
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	//printf("bing\n");
	//printf("bong\n");
	coalesce(bp);
	printf("free\n");
	checkheap(true);
	//	printf("bing\n");
	//	printf("bong\n");
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;
	size_t asize;
	//printf("bing\n");
		//printf("bong\n");
	if (size <= WSIZE)
		asize = MINBLOCKSIZE;
	else
		asize = (2 * DSIZE) + WSIZE * ((size + (WSIZE - 1)) / WSIZE);   /* 32 + 8 * ((size + 7) / 8) */

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		mm_free(ptr);
		
		return NULL;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(ptr == NULL) {
		return (mm_malloc(size));
	}

	/* Get the size of the original block */
	oldsize = GET_SIZE(HDRP(ptr));

	/* if size of block equals necessary space or cannot be divided into 2 blocks, return ptr */
	if (asize == oldsize || oldsize - asize <= MINBLOCKSIZE)
		return ptr;

	/* if oldsize is larger than asize, shrink the block size */
	if(oldsize >= asize)
	{
		PUT(HDRP(ptr), PACK(size, 1));
		PUT(FTRP(ptr), PACK(size, 1));
		PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldsize-size, 1));
		mm_free(NEXT_BLKP(ptr));
		return ptr;
	}

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(newptr == NULL) {
		return NULL;
	}

	/* Copy the old data. */
	if(size < oldsize) 
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);
	//	printf("bing\n");
	//	printf("bong\n");

	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of block to be added to beginning of free list
 *
 * Effects:
 *    1) Sets pointer for prev free block to be null (since it's at the head of free list)
 *    2) Sets pointer for next free block to be at beginning of free list
 *    3) Sets pointer for prev free block of the old block to be the new block
 *
 *    adds a block to the beginning of the free list
 */
static void 
addToBeginningOfFreeList(void *bp)
{
	//	printf("bing\n");
		//	printf("bong\n");
	if (free_listp == NULL)
		free_listp = bp;
	else{
	SETNEXT(bp) = free_listp; //Sets next ptr to start of free list
	SETPREV(free_listp) = bp; //Sets current's prev to new block
	SETPREV(bp) = NULL; // Sets prev pointer to NULL
	free_listp = bp;
	}
	//printf("bing\n");
	//	printf("bong\n");
}

/* Requires:
 * "bp" is the address of block to be removed from free list
 * has_prev, 0 for no prev block, 1 for has prev block
 *
 * Effects:
 *    Removes block from free list by resetting pointers and unallocating block
 */
static void 
removeBlockFromList(void *bp)
{
	//printf("bing\n");
	//printf("bong\n");

	if (GET(GETPREV(bp))) {
		if (GET(GETNEXT(bp)))
			SETNEXT(*GETPREV(bp)) = *GETNEXT(bp);
		else
			SETNEXT(*GETPREV(bp)) = NULL;
		SETPREV(*GETNEXT(bp)) = *GETPREV(bp);
	}
	else {
		free_listp = *GETNEXT(bp); 
		*(char **)(heap_arrayp + free_list_place * WSIZE) = free_listp;
		SETPREV(*GETNEXT(bp)) = bp;
	}
       
	//printf("bing\n");
	//	printf("bong\n");
}

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void 
*coalesce(void *bp)
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	//printf("bing\n");
	//	printf("bong\n");

	if (PREV_BLKP(bp) == bp) {
		prev_alloc = true;
	}

	/* a-a-a */
	/* insert self at beginning of free list */
	if (prev_alloc && next_alloc) {                 /* Case 1 */
		addToBeginningOfFreeList(bp);
	} 

	/* a-a-f */
	/* splice out next, coalesce self and next, and add to beginning of free list */
	else if (prev_alloc && !next_alloc)             /* Case 2 */
	{			
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		removeBlockFromList(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		addToBeginningOfFreeList(bp);
	}

	/* f-a-a */
	/* splice out prev, coalesce with self, and add to beginning of free list */
	else if (!prev_alloc && next_alloc)             /* Case 3 */
	{		
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		removeBlockFromList(bp);
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		addToBeginningOfFreeList(bp);
	}

	/* f-a-f */
	/* splice out prev and next, coalesce with self, and add to beginning of list */
	else if (!prev_alloc && !next_alloc)                                       /* Case 4 */
	{		
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
				GET_SIZE(HDRP(NEXT_BLKP(bp)));
		removeBlockFromList(PREV_BLKP(bp));
		removeBlockFromList(NEXT_BLKP(bp));
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		addToBeginningOfFreeList(bp);
	}

       	free_listp = bp;           /* start of the new free list is at the block that has been put at front of list */
	*(char **)(heap_arrayp + free_list_place * WSIZE) = free_listp;
	//printf("bing\n");
	//	printf("bong\n");
	return bp;

}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;
	//printf("bing\n");
	//	printf("bong\n");
	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

	if (size < MINBLOCKSIZE) {
		size = MINBLOCKSIZE;
	}
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	//printf("bing\n");
	//	printf("bong\n");
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{	//printf("bing\n");
	//	printf("bong\n");
	void *bp;
	for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = *GETNEXT(bp))
	{
		//printf("bing\n");
		//printf("%p\n", bp);
	if (asize <= GET_SIZE(HDRP(bp)))/*thea very first problem is located HErerherhahre a**********/
			return bp;
	else
			return NULL;
		//printf("bing\n");
		//printf("bong\n");
    	}
	//	printf("bing\n");
	//	printf("bong\n");
	return NULL;
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void 
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   
	//printf("dong\n");
	//printf("step\n");
	if ((csize - asize) >= (MINBLOCKSIZE)) { 
		//printf("step\n");
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		//printf("step\n");
		removeBlockFromList(bp);
		//printf("step\n");
		if (GET(GETNEXT(bp))){
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		coalesce(bp);
		} else
			return;
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		//printf("ding111\n");
		removeBlockFromList(bp);
	}
	//printf("ding\n");

}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */

static void 
checkblock(void *bp)
{
	if ((uintptr_t)bp % WSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */

void 
checkheap(bool verbose) 
{
	void *bp;

	heap_listp = (*(char **)(heap_arrayp + free_list_place * WSIZE));

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != MINBLOCKSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = *GETNEXT(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}


/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void printblock(void *bp)
{
	bool halloc, falloc;
	size_t hsize, fsize;

	//checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	       hsize, (halloc ? 'a' : 'f'), 
	       fsize, (falloc ? 'a' : 'f'));
}

static int 
log_2(unsigned int n) 
{
  int pos = 0;
  if (n >= 1<<16) { n >>= 16; pos += 16; }
  if (n >= 1<< 8) { n >>=  8; pos +=  8; }
  if (n >= 1<< 4) { n >>=  4; pos +=  4; }
  if (n >= 1<< 2) { n >>=  2; pos +=  2; }
  if (n >= 1<< 1) {           pos +=  1; }
  return ((n == 0) ? (-1) : pos);
}

static int 
placement(unsigned int n)
{
	if (n <= 2) 
		return 0;
	else if (n <= 3)
		return 1;
	else if (n <= 4)
		return 2;
	else if (n <= 8)
		return 3;
	else if (n <= 16)
		return 4;
	else if (n <= 32)
		return 5;
	else if (n <= 64)
		return 6;
	else if (n <= 128)
		return 7;
	else 
		return -1;
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
