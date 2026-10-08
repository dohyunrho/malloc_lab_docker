/*
 * Implicit free list allocator
 * - 8-byte alignment
 * - Next-fit search
 * - Block splitting
 * - Immediate boundary-tag coalescing
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "ateam",
    "Harry Bovik",
    "bovik@cs.cmu.edu",
    "",
    ""
};

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

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
#define FTRP(bp) \
    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) \
    ((char *)(bp) + GET_SIZE(HDRP(bp)))

#define PREV_BLKP(bp) \
    ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

static char *heap_listp;
static char *rover;  /* next-fit 탐색 위치 */

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - 힙 초기화
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

    /*
     * extend_heap도 coalesce를 호출하므로
     * 그전에 rover를 초기화한다.
     */
    rover = heap_listp;

    /* 초기 가용 블록 생성 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * extend_heap - 새 가용 블록으로 힙 확장
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 8바이트 정렬을 위해 짝수 워드로 올림 */
    size = (words % 2)
        ? (words + 1) * WSIZE
        : words * WSIZE;

    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    /* 기존 에필로그 위치를 새 블록의 헤더로 사용 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    /* 새 에필로그 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
 * mm_free - 블록 해제 후 인접 가용 블록과 병합
 */
void mm_free(void *bp)
{
    size_t size;

    if (bp == NULL)
        return;

    size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);
}

/*
 * coalesce - 인접 가용 블록을 병합하고
 * 병합된 블록의 payload 시작 주소를 반환
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1: 앞뒤 모두 할당 상태 */
    if (prev_alloc && next_alloc) {
        return bp;
    }

    /* Case 2: 다음 블록만 가용 상태 */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* Case 3: 이전 블록만 가용 상태 */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    /* Case 4: 앞뒤 모두 가용 상태 */
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))
              + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    /*
     * 병합으로 rover가 블록 내부에 들어갔다면
     * 병합된 블록의 시작으로 옮긴다.
     */
    if (rover > (char *)bp &&
        rover < NEXT_BLKP(bp)) {
        rover = (char *)bp;
    }

    return bp;
}

/*
 * mm_malloc - 가용 블록을 찾아 할당
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void *bp;

    if (size == 0)
        return NULL;

    /* 헤더·푸터 포함, 8바이트 정렬, 최소 16바이트 */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = ALIGN(size + DSIZE);

    /* next-fit으로 기존 가용 블록 탐색 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 적합한 블록이 없으면 힙 확장 */
    extendsize = (asize > CHUNKSIZE)
        ? asize
        : CHUNKSIZE;

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);

    /* 확장 후 할당한 블록을 다음 탐색의 시작으로 설정 */
    rover = (char *)bp;

    return bp;
}

/*
 * find_fit - next-fit 탐색
 *
 * rover부터 힙 끝까지 탐색하고,
 * 처음으로 돌아와 시작 위치 직전까지 탐색한다.
 */
static void *find_fit(size_t asize)
{
    char *start = rover;

    /* rover부터 에필로그 직전까지 탐색 */
    for (; 
         GET_SIZE(HDRP(rover)) > 0;
         rover = NEXT_BLKP(rover)) {

        if (!GET_ALLOC(HDRP(rover)) &&
            GET_SIZE(HDRP(rover)) >= asize) {
            return rover;
        }
    }

    /* 힙 처음부터 원래 시작 위치 직전까지 탐색 */
    for (rover = heap_listp;
         rover < start;
         rover = NEXT_BLKP(rover)) {

        if (!GET_ALLOC(HDRP(rover)) &&
            GET_SIZE(HDRP(rover)) >= asize) {
            return rover;
        }
    }

    return NULL;
}

/*
 * place - 가용 블록에 할당하고 필요하면 분할
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    /* 남는 공간이 최소 블록 크기 이상이면 분할 */
    if (csize - asize >= 2 * DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        /* 남는 공간이 작으면 블록 전체를 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_realloc - 새 블록 할당, 복사, 기존 블록 해제
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
        return NULL;

    /* 기존 payload 용량 */
    copySize = GET_SIZE(HDRP(ptr)) - DSIZE;

    if (size < copySize)
        copySize = size;

    memcpy(newptr, ptr, copySize);
    mm_free(ptr);

    return newptr;
}