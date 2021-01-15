/*
 * mm.c
 *
 * Name: Agha Arib Hyder
 *
My code implementation is based off the design from our course textbook (chapter 9.9) where I am
using several static functions for basic functionality to provide assistance throughout the larger
functions, such as malloc, free, mm_init, and realloc. This design is based from an implicit free
list design to manage blocks. This design allocates both the size and whether the block is free in
the header and the footer. The prologue and epilogue blocks are also included to account for edge
cases and the pointer heap_listp is responsible for always pointing to the prologue. The malloc,
free, and mm_init functions are designed based off of the textbook code as well, but my design did
not use the coalesce function properly, so I found my program to run more effectively without it.
Since the find_fit function from the textbook was not helping my block utilization, I also removed
this to at least improve throughput if it wasn't helping my utilization of free blocks. At some
points, I removed extend_heap from some functions and immediately called mem_sbrk to extend the heap
more efficiently for throughput in some cases. Realloc was the only function I had to write completely
on my own, without aid from the textbook. If the size passed is 0 for the block pointer given to
realloc, the function simply calls free to allocate its size to 0. If the passed in block pointer given
to realloc is NULL, then the function just calls malloc to extend the heap by the requested size. If the
size passed to realloc is the same as the current block size, then the function just returns the pointer
(because it isn't being told to do anything). If none of these listed cases occur, realloc assigns a new
pointer to malloc the passed in size. Then the data is copied over from the original block to the new
block and gives it the larger of the old size and the new size. I was not able to properly implement the
use of coalesce or find fit effectively, so they were not used from the textbook code design and my goal
was to focus on improving throughput as much as possible. If I had more time, I would've focused on
coalescing blocks properly, and using a best fit design for find fit in order to improve utilization.
The heap checker checks various invariants and is particularly helpful when I run a single trace and can
follow the calls to malloc, realloc, and free in that trace to match with what is being printed to the
command prompt as the program runs. Therefore, I can see which call in the trace is corrupting the heap,
headers/footers, prologue, etc. I was able to use the heap checker to follow whether free, malloc, or
realloc is functioning properly. When one of these functions was not working properly, I would be able to
see what is happening to the heap and also which line in the trace is causing the corruption. The biggest
fault of my program design is that utilization is not amazing (find fit and coalesce aren't implemented),
but I focused on improving throughput where I could to at least make it efficient.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

size_t wordSize = 8;
size_t doubleSize = 16;
size_t dataChunk = 1<<12;
void* heap_listp;

/* What is the correct alignment? */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

//Returns max value between 2 integers (pg. 830 of textbook)
static size_t max(size_t x, size_t y) {

  if (x > y) {
    return x;
  }
  else {
    return y;
  }
}

//Pack a size and allocate bit into a word (pg. 830 of textbook)
static size_t pack(size_t size, size_t alloc) {
  return (size | alloc);
}
//Read and write a word at address p (pg. 830 of textbook)
static size_t get(void* p) {
  return (*(size_t *)(p));
}

static size_t put(void* p, size_t val) {
  return (*(size_t*)(p) = (val));
}
//Read size and allocated fields at address p (pg. 830 of textbook)
static size_t get_size(void* p) {
  return (get(p) & 0xf);
}

static size_t get_alloc(void* p) {
  return (get(p) & 0x1);
}
//Compute address of header and footer for block pointer bp (pg. 830 of textbook)
static void *hdrp(void* bp) {
  return ((char *)(bp) - wordSize);
}

static void *ftrp(void* bp) {
  return ((bp) + get_size(hdrp(bp)) - doubleSize);
}
//Compute address of next and previous blocks, given block pointer bp (pg.830 of textbook)
static void *next_blkp(void* bp) {
  return ((bp) + get_size(((bp) - wordSize)));
}

static char *prev_blkp(void* bp) {
  return ((bp) - get_size(((bp) - doubleSize)));
}

//Search free list for right-size block (pg. 856 of textbook)
static void *find_fit(size_t asize) {
  void *bp;
  void *heap_listp = mem_sbrk(4*wordSize);


  //Searching for a fit
  for (bp = heap_listp; get_size(hdrp(bp)) > 0; bp = next_blkp(bp)) {
    if (!get_alloc(hdrp(bp)) && (asize <= get_size(hdrp(bp)))) {

      return bp;
    }
  }

  //No fit found
  return NULL;
}
//Place a block in memory (pg. 856 - 857 of textbook)
static void place(void *bp, size_t asize) {
  size_t csize = get_size(hdrp(bp));
  if ((csize - asize) >= (2*doubleSize)) {
    //Place new allocated block before moving to next block
    //If remainder of the block after splitting is >= minimum block size (16), split the block
    put(hdrp(bp), pack(asize, 1));
    put(ftrp(bp), pack(asize, 1));
    bp = next_blkp(bp);
    put(hdrp(bp), pack(csize - asize, 0));
    put(ftrp(bp), pack(csize - asize, 0));
  }
  else {
    put(hdrp(bp), pack(csize, 1));
    put(ftrp(bp), pack(csize, 1));
  }
}

//Extends the heap with a new free block (pg. 831 of textbook)
static void *extend_heap(size_t words) {
  void *bp;
  size_t size = words;
  //Allocate even number of words for alignment
  size = (words % 2) ? (words + 1) * wordSize : words * wordSize;

  if ((long)(bp = mem_sbrk(size)) == -1) {
    return NULL;
  }

  //Initialize free block header/footer and epilogue header
  put(hdrp(bp), pack(size, 0));
  put(ftrp(bp), pack(size, 0));
  put(hdrp(next_blkp(bp)), pack(0, 1));

  return bp;
}

/*
 * Initialize: returns false on error, true on success.
 */
//Initialize the memory system (pg. 831 of textbook)
bool mm_init(void)
{
    /* IMPLEMENT THIS */
    //Return NULL if you cannot create heap space
    if ((heap_listp = mem_sbrk(4*wordSize)) == (void *)-1) {
      return false;
    }
    //Initialize header and set next and prev pointers
    put(heap_listp, 0);
    put(heap_listp + (1*wordSize), pack(doubleSize, 1));
    put(heap_listp + (2*wordSize), pack(doubleSize, 1));
    put(heap_listp + (3*wordSize), pack(0, 1));
    heap_listp += (2*wordSize);
    //Return NULL if you cannot create heap space
    if (extend_heap(dataChunk/wordSize) == NULL) {
      return false;
    }
    return true;
}

/*
 * malloc
 */
 //Allocate more memory to the heap (pg. 834 of textbook)
void* malloc(size_t size)
{
    /* IMPLEMENT THIS */

  size_t asize;

  char *bp;

  if (size == 0) {
    return NULL;
  }
  //Adjust block size to include overhead and alignment
  if (size <= doubleSize) {
    asize = 2*doubleSize;
  }
  else {
    asize = doubleSize * ((size + (doubleSize) + (doubleSize - 1)) / doubleSize);
  }
  //immediately extends heap for aligned size
  bp = mem_sbrk(asize);

  place(bp, asize);

  return bp;
}

/*
 * free
 */
//Free a block of memory in the heap (pg. 833 of textbook)
void free(void* ptr)
{
    /* IMPLEMENT THIS */
  if (ptr == NULL) {
    return;
  }
  //Get size of block from given pointer
  size_t size = get_size(hdrp(ptr));
  //Free header and footer
  put(hdrp(ptr), pack(size, 0));
  put(ftrp(ptr), pack(size, 0));

}

/*
 * realloc
 */
//Returns a pointer to an allocated block of a given size
//If size is 0, acts as free()
//If ptr is NULL, acts as malloc()
void* realloc(void* oldptr, size_t size) {
    /* IMPLEMENT THIS */

  void *newptr;
  //When size = 0, realloc works the same way as free
  if (size == 0) {
    free(oldptr);
    return NULL;
  }
  //when oldptr is NULL, realloc just acts as malloc
  if (oldptr == NULL) {
    return malloc(size);
  }

  //size doesn't need to change, so return the original pointer
  if (size == get_size(hdrp(oldptr))) {
    return oldptr;
  }

  newptr = malloc(size);

  //copy over data from block pointed to by oldptr
  memcpy(newptr, oldptr, max(size, get_size(hdrp(oldptr))));
  //free old block
  free(oldptr);

  return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
//Checks heap invariants for various function calls in the program
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */
    /* IMPLEMENT THIS */
        void* ptr = heap_listp;
        //Display the start and end of the heap along with the line number
        if (lineno) {
          dbg_printf("\nHEAP: First Byte %p  Last Byte %p\n", mem_heap_lo(), mem_heap_hi);
          dbg_printf("Line #: %d\n", lineno);
        }
        //Display how the size of the heap is changing, along with the line number
        if (lineno) {
          dbg_printf("\nHEAP SIZE: %zu\n", mem_heapsize());
          dbg_printf("Line #: %d\n", lineno);
        }
        //Verify whether the pointer heap_listp is in the heap or not
        if (lineno) {
          if (in_heap(ptr) != true) {
            dbg_printf("\nPointer is not in heap\n");
          }
          else {
            dbg_printf("\nPointer is in heap\n");
          }
          dbg_printf("Line #: %d\n", lineno);
        }
        //Verify if the heap_listp pointer is properly aligned as it's address changes by running a trace
        if (lineno) {
          if (aligned(ptr) != true) {
            dbg_printf("\nPointer is not aligned\n");
          }
          else {
            dbg_printf("\nPointer is aligned\n");
          }
          dbg_printf("Line #: %d\n", lineno);
        }
        //Checks whether the header and footer of the block are matching or different
        if (lineno) {
          if (get(hdrp(ptr)) != get(ftrp(ptr))) {
            dbg_printf("\nHeader and footer are different\n");
          }
          else {
            dbg_printf("\nHeader and footer are the same\n");
          }
          dbg_printf("Line #: %d\n", lineno);
        }
        //Checks whether the prologue value is correct
        if (lineno) {
          if(get_size(hdrp(ptr)) != 16) {
            dbg_printf("\nPrologue is incorrect\n");
          }
          else if (get_alloc(hdrp(ptr)) == NULL) {
            dbg_printf("\nPrologue is incorrect\n");
          }
          else {
            dbg_printf("\nPrologue is correct\n");
          }
          dbg_printf("Line #: %d\n", lineno);
        }
        //Checks if the next block pointer is within the heap bounds
        if (lineno) {
          if (next_blkp(ptr) > mem_heap_hi() || next_blkp(ptr) < mem_heap_lo()) {
            dbg_printf("\nNext block pointer is outside of heap\n");
          }
          else {
            dbg_printf("\nNext block pointer is within heap bounds\n");
          }
          dbg_printf("Line #: %d\n", lineno);
        }
        //Checks if the previous block pointer is within the heap bounds
        if (lineno) {
          if (prev_blkp(ptr) > mem_heap_hi() || prev_blkp(ptr) < mem_heap_lo()) {
            dbg_printf("\nNext block pointer is outside of heap\n");
          }
          else {
            dbg_printf("\nNext block pointer is within heap bounds\n");
          }
          dbg_printf("Line #: %d\n", lineno);
        }
        //Checks if epilogue is correct
        if (lineno) {
          if (get_size(hdrp(ptr))) {
            dbg_printf("\nEpilogue is incorrect\n");
          }
          else if (get_alloc(hdrp(ptr)) == NULL) {
            dbg_printf("\nEpilogue is incorrect\n");
          }
          else {
            dbg_printf("\nEpilogue is correct\n");
          }
          dbg_printf("Line #: %d\n", lineno);
        }
#endif /* DEBUG */
    return true;
}

