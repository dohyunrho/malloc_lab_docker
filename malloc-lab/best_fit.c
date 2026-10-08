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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

#define PACK(size, alloc) ((size) | (alloc))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET(p) (*(unsigned int *)(p))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/* bp는 payload의 시작 주소 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) \
    ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) \
    ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

static void *coalesce(void *bp);
static char *heap_listp;
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 패딩 + 프롤로그 헤더·푸터 + 에필로그 헤더 */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));

    heap_listp += 2 * WSIZE;

    /* 초기 가용 블록 생성 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * extend_heap - 새 가용블록으로 힙 확장하기
 */

 static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    size = (words % 2) ? (words + 1) *WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
    
    return coalesce(bp);
}

/*
 * mm_free - 블록을 해제하고 인접 가용블록과 병합
 */
 void mm_free(void *bp)
 {
    if (bp == NULL)
        return;

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);
 }

/*
 * coalesce - 인접 가용 블록을 병합하고 병합된 블록의
 *            payload 시작 주소를 반환한다.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* 1. 앞뒤 모두 할당 상태 */
    if (prev_alloc && next_alloc) {
        return bp;
    }

    /* 2. 다음 블록만 가용 상태 */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* 3. 이전 블록만 가용 상태 */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* 4. 앞뒤 모두 가용 상태 */
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))
              + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void *bp;

    if (size == 0)
        return NULL;

    /* 헤더·푸터 8바이트 포함, 8바이트 정렬, 최소 16바이트 */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = ALIGN(size + DSIZE);

    /* 기존 가용 블록에서 찾기 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 없으면 최소 CHUNKSIZE만큼 힙 확장 */
    extendsize = (asize > CHUNKSIZE) ? asize : CHUNKSIZE;

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

/*
 * find_fit - best-fit 탐색
 * 요청 크기 이상인 가용 블록 중 가장 작은 블록을 반환
 */
static void *find_fit(size_t asize)
{
    void *bp;
    void *best_bp = NULL;
    size_t best_size = 0;

    for (bp = heap_listp;
         GET_SIZE(HDRP(bp)) > 0;
         bp = NEXT_BLKP(bp)) {

        size_t csize = GET_SIZE(HDRP(bp));

        /* 할당된 블록이나 크기가 부족한 블록은 제외 */
        if (GET_ALLOC(HDRP(bp)) || csize < asize)
            continue;

        /* 지금까지 찾은 후보보다 작으면 갱신 */
        if (best_bp == NULL || csize < best_size) {
            best_bp = bp;
            best_size = csize;

            /* 요청 크기와 같으면 더 좋은 후보가 없으므로 종료 */
            if (csize == asize)
                return best_bp;
        }
    }

    return best_bp;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    /* 남는 공간으로 최소 크기의 가용 블록을 만들 수 있는가? */
    if (csize - asize >= 2 * DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        /* 남는 공간이 너무 작으면 블록 전체를 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t copySize;

    if (ptr == NULL)
        return mm_malloc(size);

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;  /* 기존 블록은 그대로 유지 */

    /* 전체 블록 크기에서 헤더·푸터 크기를 제외 */
    copySize = GET_SIZE(HDRP(ptr)) - DSIZE;

    if (size < copySize)
        copySize = size;

    memcpy(newptr, ptr, copySize);
    mm_free(ptr);

    return newptr;
}