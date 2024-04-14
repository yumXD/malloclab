/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
        /* Team name */
        "ateam",
        /* First member's full name */
        "Harry Bovik",
        /* First member's email address */
        "bovik@cs.cmu.edu",
        /* Second member's full name (leave blank if none) */
        "",
        /* Second member's email address (leave blank if none) */
        ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE       4
#define DSIZE       8
#define CHUNKSIZE   (1 << 12)

#define MAX(x, y)   ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)   ((size) | (alloc))

#define GET(p)  (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)    (GET(p) & ~0x7)
#define GET_ALLOC(p)   (GET(p) & 0x1)

#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)   (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)))

static char *heap_listp;

static void *extend_heap(size_t words);

static void *coalesce(void *bp);

static void *find_fit(size_t asize);

static void place(void *bp, size_t asize);

/* 다음으로 검색할 위치를 저장할 전역 변수 */
static char *next_fit_ptr = NULL;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    /* 초기 빈 힙 생성 */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1)
        return -1;
    PUT(heap_listp, 0);                        /* 정렬을 위한 여백 삽입 */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 헤더 설정 */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 푸터 설정 */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* 에필로그 헤더 설정 */
    heap_listp += (2 * WSIZE);
    /* 다음으로 검색할 위치 초기화 */
    next_fit_ptr = heap_listp;

    /* CHUNKSIZE 바이트의 빈 힙을 추가로 확장 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;      /* 조정된 블록 크기 */
    size_t extendsize; /* 적합한 블록을 찾지 못했을 때 확장할 힙의 크기 */
    char *bp;

    /* 불필요한 요청 무시 */
    if (size == 0)
        return NULL;

    /* 오버헤드와 정렬 요구 사항을 포함한 블록 크기 조정 */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* 빈 블록을 검색하여 적합한 블록을 찾음 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 적합한 블록을 찾지 못했을 경우, 힙을 확장하여 새로운 블록 할당 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));

    /* 할당 비트를 해제하여 블록을 사용 가능한 빈 블록으로 표시 */
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    /* 빈 블록을 병합하여 연속된 빈 블록을 만듦 */
    coalesce(ptr);
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* 요청된 워드 수를 워드 단위로 정렬 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 새로운 블록의 헤더와 푸터 설정 */
    PUT(HDRP(bp), PACK(size, 0));         /* 블록 헤더 설정 */
    PUT(FTRP(bp), PACK(size, 0));         /* 블록 푸터 설정 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* 새로운 에필로그 헤더 설정 */

    /* 만약 이전 블록이 비어있으면, 새로운 블록과 병합 */
    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1: 이전 블록과 다음 블록이 모두 할당됨 */
        return bp;
    } else if (prev_alloc && !next_alloc) {    /* Case 2: 다음 블록만 비어 있음 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {    /* Case 3: 이전 블록만 비어 있음 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {                                   /* Case 4: 이전 블록과 다음 블록이 모두 비어 있음 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* 다음 검색 위치 업데이트 */
    next_fit_ptr = bp;
    return bp;
}

static void *find_fit(size_t asize) {
    char *bp;

    /* 다음으로 검색할 위치부터 시작 */
    if (next_fit_ptr == NULL)
        next_fit_ptr = heap_listp;

    /* 저장된 위치부터 시작하여 빈 블록을 검색 */
    for (bp = next_fit_ptr; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            /* 적합한 블록을 찾으면, 다음 검색 위치 업데이트 */
            next_fit_ptr = bp;
            return bp;
        }
    }

    /* 저장된 위치부터 검색하여 빈 블록을 찾지 못하면, 힙의 시작부터 시작하여 검색 */
    for (bp = heap_listp; bp < next_fit_ptr; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            /* 적합한 블록을 찾으면, 다음 검색 위치 업데이트 */
            next_fit_ptr = bp;
            return bp;
        }
    }

    /* 빈 블록을 찾지 못한 경우 */
    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        /* 남은 부분이 충분히 크면 블록을 분할 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        /* 남은 부분이 충분히 크지 않으면 블록을 모두 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
