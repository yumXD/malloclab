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
#define PUT(p, val)  (*(unsigned int *)(p) = (unsigned int)(val))

#define GET_SIZE(p)    (GET(p) & ~0x7)
#define GET_ALLOC(p)   (GET(p) & 0x1)

#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)   (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)))

#define FREE_SUCC(bp)  (*(void**)(bp + WSIZE))
#define FREE_PRED(bp)  (*(void**)(bp))

static char *heap_listp = NULL;
static char *free_listp = NULL;

static void *extend_heap(size_t words);

static void *coalesce(void *bp);

static void *find_fit(size_t asize);

static void place(void *bp, size_t asize);

static void removeBlock(void *bp);

static void putFreeBlock(void *bp);

/*
 * mm_init - initialize the malloc package.
 */
/* 메모리 할당자를 초기화 */
int mm_init(void) {
    // 초기 힙 공간을 할당합니다.
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *) -1)
        return -1;

    // 프롤로그 블록 설정
    PUT(heap_listp, 0);                                      // 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1));       // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), NULL);                     // 프리 리스트의 이전 블록 포인터
    PUT(heap_listp + (3 * WSIZE), NULL);                     // 프리 리스트의 다음 블록 포인터
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1));       // 프롤로그 푸터
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));               // 에필로그 헤더

    // 프리 리스트 포인터 설정
    free_listp = heap_listp + (2 * WSIZE);

    // 추가적인 힙 공간을 할당합니다.
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
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
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/* 힙을 확장하여 새로운 가용 블록을 생성 */
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

/* 주어진 블록과 그 다음 블록이 가용 상태일 때 이를 병합 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        putFreeBlock(bp);
        return bp;
    } else if (prev_alloc && !next_alloc) {    /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removeBlock(NEXT_BLKP(bp));           // 다음 블록을 가용 블록 리스트에서 제거합니다.
        PUT(HDRP(bp), PACK(size, 0));         // 병합된 블록의 헤더 설정
        PUT(FTRP(bp), PACK(size, 0));         // 병합된 블록의 푸터 설정
    } else if (!prev_alloc && next_alloc) {    /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        removeBlock(bp);                      // 이전 블록을 가용 블록 리스트에서 제거합니다.
        PUT(HDRP(bp), PACK(size, 0));         // 병합된 블록의 헤더 설정
        PUT(FTRP(bp), PACK(size, 0));         // 병합된 블록의 푸터 설정
    } else {                                   /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        removeBlock(NEXT_BLKP(bp));           // 다음 블록을 가용 블록 리스트에서 제거합니다.
        bp = PREV_BLKP(bp);
        removeBlock(bp);                      // 이전 블록을 가용 블록 리스트에서 제거합니다.
        PUT(HDRP(bp), PACK(size, 0));         // 병합된 블록의 헤더 설정
        PUT(FTRP(bp), PACK(size, 0));         // 병합된 블록의 푸터 설정
    }
    putFreeBlock(bp);                          // 병합된 블록을 가용 블록 리스트의 맨 앞에 추가합니다.
    return bp;
}


/* 요청된 크기에 맞는 가용 블록을 찾기 */
static void *find_fit(size_t asize) {
    void *bp;

    /* 가용 블록 리스트를 순회하며 요청된 크기보다 크거나 같은 가용 블록을 찾습니다. */
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = FREE_SUCC(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp; /* 찾은 가용 블록의 포인터를 반환합니다. */
        }
    }

    /* 적합한 가용 블록을 찾지 못한 경우 NULL 반환 */
    return NULL;
}

/* 요청된 크기에 맞는 가용 블록을 할당하고, 필요한 경우 분할 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    removeBlock(bp); // 기존 가용 블록을 리스트에서 제거합니다.

    if ((csize - asize) >= (2 * DSIZE)) {
        // 요청된 크기보다 큰 가용 블록을 분할하여 할당
        PUT(HDRP(bp), PACK(asize, 1));             // 할당된 블록 헤더 설정
        PUT(FTRP(bp), PACK(asize, 1));             // 할당된 블록 푸터 설정
        bp = NEXT_BLKP(bp);                        // 다음 블록으로 이동
        PUT(HDRP(bp), PACK((csize - asize), 0));   // 나머지 가용 블록 헤더 설정
        PUT(FTRP(bp), PACK((csize - asize), 0));   // 나먼지 가용 블록 푸터 설정
        putFreeBlock(bp);                          // 나머지 가용 블록을 리스트의 맨 앞에 추가
    } else {
        // 요청된 크기와 같거나 작은 가용 블록을 할당
        PUT(HDRP(bp), PACK(csize, 1));             // 할당된 블록 헤더 설정
        PUT(FTRP(bp), PACK(csize, 1));             // 할당된 블록 푸터 설정
    }
}

/* 주어진 블록을 가용 블록 리스트에서 제거 */
static void removeBlock(void *bp) {
    /* 주어진 블록이 리스트의 맨 앞에 있는 경우 */
    if (bp == free_listp) {
        FREE_PRED(FREE_SUCC(bp)) = NULL; /* 리스트의 헤더를 업데이트하여 첫 번째 블록을 변경 */
        free_listp = FREE_SUCC(bp);
    } else {
        /* 주어진 블록이 리스트의 맨 앞에 있지 않은 경우 */
        /* 주어진 블록의 이전 블록과 다음 블록을 연결하여 리스트에서 제거 */
        FREE_SUCC(FREE_PRED(bp)) = FREE_SUCC(bp);
        FREE_PRED(FREE_SUCC(bp)) = FREE_PRED(bp);
    }
}

/* 주어진 블록을 가용 블록 리스트의 맨 앞에 추가 */
static void putFreeBlock(void *bp) {
    FREE_SUCC(bp) = free_listp; /* 새로운 가용 블록의 다음 포인터를 기존의 리스트의 첫 번째 블록을 가리킴 */
    FREE_PRED(bp) = NULL; /* 새로운 가용 블록의 이전 포인터를 NULL로 설정 */
    FREE_PRED(free_listp) = bp; /* 기존의 리스트의 첫 번째 블록의 이전 포인터를 새로운 가용 블록을 가리킴 */
    free_listp = bp; /* 리스트의 헤더를 새로운 가용 블록으로 업데이트 */
}