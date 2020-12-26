/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * Header (8 bytes):
 * ________________
 * |size________|b|
 *
 * b is 1 byte and stores extra info
 *
 * Allocated Block (Min: 16 bytes):
 * ________________
 * |____Header____|
 * |              |
 * |    Payload   |
 * |______________|
 *
 * Free Block (Min: 32 bytes):
 * ________________
 * |____Header____|
 * | prev pointer |
 * | next pointer |
 * |____footer____|
 *
 * Mini Free Block (Min: 16 bytes):
 * __________________
 * |____Header______|
 * |                |
 * |miniNext pointer|
 * |________________|
 *
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Eric Gan <ehgan>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/** @brief length of segList array */
static const size_t segLength = 14;

/**
 * @brief General size of a page (4096 bytes)
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * @brief Used to isolate the 0th bit of header (Storing alloc status)
 */
static const word_t alloc_mask = 0x1;

/**
 * @brief Used to isolate the 1st bit of header (Storing alloc status of
 * previous block)
 */
static const word_t prev_alloc_mask = 0x2;

/**
 * @brief Used to isolate the 2nd bit of header (Storing mini-block status)
 */
static const word_t mini_mask = 0x4;

/**
 * @brief Used to isolate the 3rd bit of header (Storing mini-block status of
 * previous block)
 */
static const word_t prev_mini_mask = 0x8;

/**
 * @brief Isolate out the first byte of header to get size because header
 * because size of block is at least 2 bytes so right-most byte stores extra
 * information
 */
static const word_t size_mask = ~(word_t)0xF;

/**
 * @brief Defining struct block for use in other struct definitions
 */
struct block;

/**
 * @brief Defining struct that contains pointers next and prev in
 * between regular, non mini free blocks in circular doubly-linked list
 */
typedef struct freePointers {
    struct block *next;
    struct block *prev;
} freePointers_t;

/**
 * @brief Defining union that contains pointers for regular, non mini
 * free blocks and a pointer to the next mini free block, depending on if
 * the free block is regular size or a mini block
 */
typedef union smallerPointers {
    freePointers_t freePointers;
    struct block *miniNext;
} smallerPointers_t;

/** @brief Represents the header and free pointers/payload of one block in the
 * heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A union that represents the possible pointer(s) for free
     * block/payload
     */
    union {
        smallerPointers_t pointers;
        char payload[0];
    };

} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/** @brief Pointer to seg list for free blocks. Length of 14 to fit allowed
 * global variable size */
static block_t *segFreeLists[14];

/** @brief Pointer to linkedlist of mini free blocks */
static block_t *miniFreeList = NULL;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the size, alloc status, alloc status of previous block, mini
 * status, and mini status of previous block of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for headers.
 * Also used for footers if block is a regular free block.
 *
 * The allocation status is packed into the lowest bit (0th bit) of the word.
 * The allocation status of previous block is packed into the 1st bit of the
 * word. The mini-block status is packed into the 2nd of the word. The
 * mini-block status of previous block is packed into the 3rd bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @param[in] prev_alloc True if the previous block is allocated
 * @param[in] mini True if the block is mini free block
 * @param[in] prev_mini True if the previous block is mini free block
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool mini,
                   bool prev_mini) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    if (prev_alloc) {
        word |= prev_alloc_mask;
    }
    if (mini) {
        word |= mini_mask;
    }
    if (prev_mini) {
        word |= prev_mini_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit (0th bit) of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns the allocation status of previous block given a header value.
 *
 * This is based on the 1st bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the previous block
 */
static bool extract_prev_alloc(word_t word) {
    return (bool)((word & prev_alloc_mask) >> 1);
}

/**
 * @brief Returns the allocation status of previous block, based on current
 * blocks header.
 * @param[in] block
 * @return The allocation status of the previous block
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}

/**
 * @brief Returns the mini-block status of a given header value.
 *
 * This is based on the 2nd bit of the header value.
 *
 * @param[in] word
 * @return The mini-block status correpsonding to the word
 */
static bool extract_mini(word_t word) {
    return (bool)((word & mini_mask) >> 2);
}

/**
 * @brief Returns the mini-block status of a block, based on its header.
 * @param[in] block
 * @return The mini-block status of the block
 */
static bool get_mini(block_t *block) {
    return extract_mini(block->header);
}

/**
 * @brief Returns the mini-block status of previous block given a header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The mini-block status correpsonding to the previous word
 */
static bool extract_prev_mini(word_t word) {
    return (bool)((word & prev_mini_mask) >> 3);
}

/**
 * @brief Returns the mini-block status of previous block, based on current
 * blocks header.
 * @param[in] block
 * @return The mini-block status of the previous block
 */
static bool get_prev_mini(block_t *block) {
    return extract_prev_mini(block->header);
}

/**
 * @brief Sets the prev_alloc status of current block
 * @param[in] block
 * @param[in] prev_alloc status to be set
 * @param[out] block with prev_alloc status set to input
 */
static void set_prev_alloc(block_t *block, bool prev_alloc) {
    block->header = pack(get_size(block), get_alloc(block), prev_alloc,
                         get_mini(block), get_prev_mini(block));
}

/**
 * @brief Sets the prev_mini status of current block
 * @param[in] block
 * @param[in] prev_mini status to be set
 * @param[out] block with prev_mini status set to input
 */
static void set_prev_mini(block_t *block, bool prev_mini) {
    block->header = pack(get_size(block), get_alloc(block),
                         get_prev_alloc(block), get_mini(block), prev_mini);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true, true, true, true);
}

/**
 * @brief Removes the current free block from the circular doubly linked list
 * that it is contained in. Also already assumes that the input block is a free
 * block that is in the segmented linked lists.
 * @param[in] block to be removed (freed block)
 * @param[out] Segmented linked lists with the input block removed
 */
static void remove_from_freeList(block_t *block) {
    size_t index;
    size_t exponent =
        4; // exponent for smallest class size in seglist (2^4 = 16)
    size_t compareSize = 16; // smallest class size in seglist

    // finding index of the linked list that block to removed is in, based on
    // size
    while (compareSize <= get_size(block)) {
        exponent++;
        compareSize = (compareSize << 1);
    }
    if (exponent - 5 > (segLength - 1)) {
        index = (segLength - 1);
    } else {
        index = exponent - 5;
    }

    // if linkedlist at index is only one free block/node, remove and set to
    // NULL
    if (block->pointers.freePointers.next == block &&
        block->pointers.freePointers.prev == block) {
        segFreeLists[index] = NULL;
        block->pointers.freePointers.next = NULL;
        block->pointers.freePointers.prev = NULL;
        return;
    }

    // otherwise, adjust pointers to remove block from circular, doubly linked
    // list
    block_t *blockPrev = block->pointers.freePointers.prev;
    if (block == segFreeLists[index]) {
        blockPrev = segFreeLists[index]->pointers.freePointers.prev;
        segFreeLists[index] = segFreeLists[index]->pointers.freePointers.next;
        blockPrev->pointers.freePointers.next = segFreeLists[index];
        segFreeLists[index]->pointers.freePointers.prev = blockPrev;
    } else if (block->pointers.freePointers.next == segFreeLists[index]) {
        blockPrev->pointers.freePointers.next = segFreeLists[index];
        segFreeLists[index]->pointers.freePointers.prev = blockPrev;
    } else {
        block_t *blockNext = block->pointers.freePointers.next;
        blockPrev->pointers.freePointers.next = blockNext;
        blockNext->pointers.freePointers.prev = blockPrev;
    }

    // completely isolate removed block by setting next and prev pointers to
    // NULL
    block->pointers.freePointers.next = NULL;
    block->pointers.freePointers.prev = NULL;
}

/**
 * @brief Removes the current mini free block from the singly linked list that
 * it is contained in. Also already assumes that the input block is a mini free
 * block that is in the linked list.
 * @param[in] mini block to be removed (freed block)
 * @param[out] singly linked list with the input block removed
 */
static void remove_from_miniFreeList(block_t *block) {
    block_t *iterator = miniFreeList;
    block_t *prev;

    // if block to removed is root of the linked list, adjust pointer to root
    if (block == miniFreeList) {
        miniFreeList = miniFreeList->pointers.miniNext;
        return;
    }

    // otherwise, iterate through list to get previous node and adjust pointers
    // to remove
    while (iterator != NULL && iterator != block) {
        prev = iterator;
        iterator = iterator->pointers.miniNext;
    }

    if (iterator == NULL)
        return;

    prev->pointers.miniNext = iterator->pointers.miniNext;
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header for all blocks and footer for regular free
 * blocks, where the location of the footer is computed in relation to the
 * header.
 *
 * Preconditions: block must be in memory that is created from mem_sbrk, size is
 * a multiple of 16
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 * @param[in] prev_alloc The allocation status of the previous block
 * @param[in] mini The mini-block status of the new block
 * @param[in] prev_mini The mini-block status of the previous block
 */
static void write_block(block_t *block, size_t size, bool alloc,
                        bool prev_alloc, bool mini, bool prev_mini) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    size_t index;
    size_t exponent =
        4; // exponent for smallest class size in seglist (2^4 = 16)
    size_t compareSize = 16; // smallest class size in seglist

    // finding index of the linked list that block is in if overwriting a freed
    // block with an alloc'd block
    while (compareSize <= size) {
        exponent++;
        compareSize = (compareSize << 1);
    }
    if (exponent - 5 > (segLength - 1)) {
        index = (segLength - 1);
    } else {
        index = exponent - 5;
    }
    if (!alloc) {
        // if freeing a non mini block, add block to its valid location in the
        // seglist
        if (!mini) {
            if (segFreeLists[index] == NULL) {
                segFreeLists[index] = block;
                segFreeLists[index]->pointers.freePointers.next =
                    segFreeLists[index];
                segFreeLists[index]->pointers.freePointers.prev =
                    segFreeLists[index];
            } else {
                block_t *last = segFreeLists[index]->pointers.freePointers.prev;
                block->pointers.freePointers.next = segFreeLists[index];
                segFreeLists[index]->pointers.freePointers.prev = block;
                block->pointers.freePointers.prev = last;
                last->pointers.freePointers.next = block;
            }
            // creating header and footer
            // setting prev_alloc of next block to false because current block
            // is free setting prev_mini of next block to false because current
            // block is not mini
            block->header = pack(size, alloc, prev_alloc, mini, prev_mini);
            word_t *footerp = header_to_footer(block);
            *footerp = pack(size, alloc, prev_alloc, mini, prev_mini);
            set_prev_alloc(find_next(block), false);
            set_prev_mini(find_next(block), false);
            // if freeing a mini block, add block to single linked list of mini
            // blocks
        } else {
            if (miniFreeList == NULL) {
                miniFreeList = block;
                block->pointers.miniNext = NULL;
            } else {
                block->pointers.miniNext = miniFreeList;
                miniFreeList = block;
            }
            // creating header
            // setting prev_alloc of next block to false because current block
            // is free setting prev_mini of next block to true because current
            // block is mini
            block->header = pack(size, alloc, prev_alloc, mini, prev_mini);
            set_prev_alloc(find_next(block), false);
            set_prev_mini(find_next(block), true);
        }
    } else {
        // if allocating into a freed block, remove block from its valid linked
        // list of freed blocks
        if (get_alloc(block) == false) {
            if (size > min_block_size) {
                remove_from_freeList(block);
            } else {
                remove_from_miniFreeList(block);
            }
        }
        // creating header
        // setting prev_alloc of next block to true because current block is
        // allocated setting prev_mini of next block to mini-block status of
        // current block
        block->header = pack(size, alloc, prev_alloc, mini, prev_mini);
        set_prev_alloc(find_next(block), true);
        set_prev_mini(find_next(block), mini);
    }
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * This function looks at current blocks surrounding blocks and combines
 * the consecutive free blocks
 * Preconditions: block is free block
 * Postconditions: there are no consecutive free blocks
 *
 * @param[in] block to be coalesced/combined with surrounding blocks (free
 * block)
 * @return the new block that is a result of combining block with surrounding
 * free blocks if there are surrounding free blocks
 */
static block_t *coalesce_block(block_t *block) {
    bool prevFree = false;
    bool nextFree = false;
    bool prevMini = get_prev_mini(block);
    block_t *prevBlock;

    // if previous block is free set prevFree to true
    if (!get_prev_alloc(block)) {
        prevFree = true;
    }

    // if next block is free and not the epilogue, set nextFree to true
    block_t *nextBlock = find_next(block);
    if (get_size(nextBlock) > 0 && get_alloc(nextBlock) == false) {
        nextFree = true;
    }

    // if previous block and next block are free, remove the free blocks
    // from the linkedlists and combine them into a new block
    if (prevFree && nextFree) {
        if (prevMini) {
            prevBlock = (block_t *)((char *)block - min_block_size);
        } else {
            prevBlock = find_prev(block);
        }
        size_t newSize =
            get_size(prevBlock) + get_size(nextBlock) + get_size(block);
        if (get_size(prevBlock) > min_block_size) {
            remove_from_freeList(prevBlock);
        } else {
            remove_from_miniFreeList(prevBlock);
        }
        if (get_size(nextBlock) > min_block_size) {
            remove_from_freeList(nextBlock);
        } else {
            remove_from_miniFreeList(nextBlock);
        }
        if (get_size(block) > min_block_size) {
            remove_from_freeList(block);
        } else {
            remove_from_miniFreeList(block);
        }
        write_block(prevBlock, newSize, false, true, false,
                    get_prev_mini(prevBlock));
        return prevBlock;
        // if previous block is free, remove the free blocks
        // from the linkedlists and combine them into a new block
    } else if (prevFree && (!nextFree)) {
        if (prevMini) {
            prevBlock = (block_t *)((char *)block - min_block_size);
        } else {
            prevBlock = find_prev(block);
        }
        size_t newSize = get_size(prevBlock) + get_size(block);
        if (get_size(prevBlock) > min_block_size) {
            remove_from_freeList(prevBlock);
        } else {
            remove_from_miniFreeList(prevBlock);
        }
        if (get_size(block) > min_block_size) {
            remove_from_freeList(block);
        } else {
            remove_from_miniFreeList(block);
        }
        write_block(prevBlock, newSize, false, true, false,
                    get_prev_mini(prevBlock));
        return prevBlock;
        // if next block is free, remove the free blocks
        // from the linkedlists and combine them into a new block
    } else if ((!prevFree) && nextFree) {
        size_t newSize = get_size(nextBlock) + get_size(block);
        if (get_size(nextBlock) > min_block_size) {
            remove_from_freeList(nextBlock);
        } else {
            remove_from_miniFreeList(nextBlock);
        }
        if (get_size(block) > min_block_size) {
            remove_from_freeList(block);
        } else {
            remove_from_miniFreeList(block);
        }
        write_block(block, newSize, false, true, false, get_prev_mini(block));
        return block;
    } else {
        return block;
    }
    return block;
}

/**
 * @brief
 *
 * This function extends the heap by the input size and
 * gives more space for more malloc calls
 *
 * @param[in] size to extend heap by
 * @return pointer to new free block that was created by heap extension
 */
static block_t *extend_heap(size_t size) {
    void *bp;
    bool mini;
    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }
    if (size >= min_block_size) {
        mini = false;
    } else {
        mini = true;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false, get_prev_alloc(block), mini,
                get_prev_mini(block));

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief
 *
 * This function splits a block into an allocated block of size asize starting
 * at block input and a free block for the rest of the block
 *
 * Preconditions: asize < size of the block and the difference should be >= 16
 * for the function to actually do anything
 *
 * @param[in] block to be split into allocated block and free block
 * @param[in] asize size of the block to be allocated in the split
 * @param[out] input block split into allocated block of size asize and a free
 * block
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    bool mini;
    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        if (asize > min_block_size) {
            mini = false;
            write_block(block, asize, true, true, false, get_prev_mini(block));
        } else {
            mini = true;
            write_block(block, asize, true, true, true, get_prev_mini(block));
        }

        block_next = find_next(block);
        if (block_size - asize > min_block_size) {
            write_block(block_next, block_size - asize, false, true, false,
                        mini);
        } else {
            write_block(block_next, block_size - asize, false, true, true,
                        mini);
        }
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * This function finds a free block that an allocated block of asize can fit
 * into and returns NULL if there is none
 *
 * Preconditions: asize >= 16
 *
 * @param[in] asize. find a free block of >= asize to fit allocated block into
 * @return free block of size >= asize
 */
static block_t *find_fit(size_t asize) {
    size_t index;
    size_t exponent =
        4; // exponent for smallest class size in seglist (2^4 = 16)
    size_t compareSize = (1 << 4); // smallest class size in seglist

    // if asize represents a mini block, check the linkedlist of mini free
    // blocks
    if (asize <= min_block_size) {
        if (miniFreeList != NULL) {
            return miniFreeList;
        }
    }
    // if no possible mini free block or asize > a mini block, look through seg
    // list size classes to find a fit
    while (compareSize <= asize) {
        exponent++;
        compareSize = (compareSize << 1L);
    }
    if (exponent - 5 > (segLength - 1)) {
        index = (segLength - 1);
    } else {
        index = exponent - 5;
    }
    if (segFreeLists[index] != NULL) {
        block_t *current = segFreeLists[index];
        if (asize <= get_size(current)) {
            return current;
        }
        current = current->pointers.freePointers.next;
        while (current != segFreeLists[index]) {
            if (asize <= get_size(current)) {
                return current;
            }
            current = current->pointers.freePointers.next;
        }
    }
    // if appropriate size class for asize contains no free blocks, move on to
    // the next size class
    index++;
    while (index <= (segLength - 1)) {
        if (segFreeLists[index] != NULL) {
            return segFreeLists[index];
        }
        index++;
    }
    return NULL;
}

/**
 * @brief This function checks if every block in the heap is within bounds
 */
bool check_within_boundary(void) {
    if (heap_start == NULL) {
        return true;
    }
    block_t *nextBlock = heap_start;
    while (nextBlock != NULL) {
        if (get_size(nextBlock) == 0) {
            return true;
        }
        nextBlock = find_next(nextBlock);
    }
    return false;
}

/**
 * @brief This function checks if prologue exists
 */
bool check_prologue(void) {
    if (heap_start == NULL) {
        return true;
    }
    word_t *footerp = find_prev_footer(heap_start);
    if (extract_size(*footerp) == 0) {
        return true;
    }
    return false;
}

/**
 * @brief This function checks if epilogue exists
 */
bool check_epilogue(void) {
    block_t *nextBlock;
    if (heap_start == NULL) {
        return true;
    }
    nextBlock = find_next(heap_start);
    while (nextBlock != NULL) {
        if (get_size(nextBlock) == 0) {
            return true;
        }
        nextBlock = find_next(nextBlock);
    }
    return false;
}

/**
 * @brief This function checks if every block is aligned correctly
 */
bool check_alignment(void) {
    if (heap_start == NULL) {
        return true;
    }
    block_t *nextBlock = heap_start;
    while (get_size(nextBlock) > 0) {
        if (get_size(nextBlock) % dsize > 0) {
            return false;
        }
        nextBlock = find_next(nextBlock);
    }
    return true;
}

/**
 * @brief This function checks if headers and footers match
 */
bool check_header_footer(void) {
    if (heap_start == NULL) {
        return true;
    }
    block_t *nextBlock = heap_start;
    while (get_size(nextBlock) > 0) {
        word_t footer = *(header_to_footer(nextBlock));
        word_t header = nextBlock->header;
        if (extract_alloc(footer) != extract_alloc(header)) {
            return false;
        }
        if (extract_size(footer) != extract_size(header)) {
            return false;
        }
        if (extract_size(footer) < min_block_size) {
            return false;
        }
        nextBlock = find_next(nextBlock);
    }
    return true;
}

/**
 * @brief This function checks if there are any consecutive free blocks
 */
bool check_consec_free(void) {
    if (heap_start == NULL) {
        return true;
    }
    block_t *nextBlock = heap_start;
    while (get_size(nextBlock) > 0 && get_size(find_next(nextBlock)) > 0) {
        if (!get_alloc(nextBlock) && !get_alloc(find_next(nextBlock))) {
            return false;
        }
        nextBlock = find_next(nextBlock);
    }
    return true;
}

/**
 * @brief This function checks if next and prev pointers in the doubly
 * linkedlists mirror each other
 */
bool check_free_pointers(void) {
    for (size_t i = 0; i < segLength; i++) {
        block_t *root = segFreeLists[i];
        if (root != NULL) {
            if (root->pointers.freePointers.next->pointers.freePointers.prev !=
                root) {
                return false;
            }
            root = root->pointers.freePointers.next;
            while (root != segFreeLists[i]) {
                if (root->pointers.freePointers.next->pointers.freePointers
                        .prev != root) {
                    return false;
                }
                root = root->pointers.freePointers.next;
            }
        }
    }
    return true;
}

/**
 * @brief This function checks if free pointers are within bounds
 */
bool check_free_location(void) {
    for (size_t i = 0; i < segLength; i++) {
        block_t *root = segFreeLists[i];
        if (root != NULL) {
            if ((char *)root < (char *)mem_heap_lo() ||
                (char *)root > (char *)mem_heap_hi()) {
                return false;
            }
            root = root->pointers.freePointers.next;
            while (root != segFreeLists[i]) {
                if ((char *)root < (char *)mem_heap_lo() ||
                    (char *)root > (char *)mem_heap_hi()) {
                    return false;
                }
                root = root->pointers.freePointers.next;
            }
        }
    }
    return true;
}

/**
 * @brief This function checks if number of free blocks in linkedlists matches
 * free blocks in heap
 */
bool check_free_count(void) {
    int pointerCount = 0;
    int heapCount = 0;
    if (heap_start == NULL) {
        return true;
    }
    block_t *nextBlock = heap_start;
    while (get_size(nextBlock) > 0) {
        if (!get_alloc(nextBlock)) {
            heapCount++;
        }
        nextBlock = find_next(nextBlock);
    }
    for (size_t i = 0; i < segLength; i++) {
        block_t *root = segFreeLists[i];
        if (root != NULL) {
            pointerCount++;
            root = root->pointers.freePointers.next;
            while (root != segFreeLists[i]) {
                pointerCount++;
                root = root->pointers.freePointers.next;
            }
        }
    }
    return pointerCount == heapCount;
}

/**
 * @brief This function checks if free blocks are in correct size class in
 * seglist
 */
bool check_correct_bucket(void) {
    for (size_t i = 0; i < segLength; i++) {
        block_t *root = segFreeLists[i];
        if (root != NULL) {
            if (i < (segLength - 1)) {
                if (get_size(root) >= (1 << (i + 5)) ||
                    get_size(root) < (1 << (i + 4))) {
                    return false;
                }
            } else {
                if (get_size(root) < (1 << (i + 4))) {
                    return false;
                }
            }
            root = root->pointers.freePointers.next;
            while (root != segFreeLists[i]) {
                if (i < (segLength - 1)) {
                    if (get_size(root) >= (1 << (i + 5)) ||
                        get_size(root) < (1 << (i + 4))) {
                        return false;
                    }
                } else {
                    if (get_size(root) < (1 << (i + 4))) {
                        return false;
                    }
                }
                root = root->pointers.freePointers.next;
            }
        }
    }
    return true;
}

/**
 * @brief
 *
 * This function is used for debugging checks if there is any point when
 * the invariant checks aren't satisfied
 *
 * @param[in] line on which error occurs
 * @return false if invariant not satisfied and prints line and error message
 */
bool mm_checkheap(int line) {
    if (!check_within_boundary()) {
        printf("%s\n", "Blocks not within heap boundaries");
        return false;
    }
    if (!check_prologue()) {
        printf("%s\n", "Prologue doesn't exist");
        return false;
    }
    if (!check_epilogue()) {
        printf("%s\n", "Epilogue doesn't exist");
        return false;
    }
    if (!check_alignment()) {
        printf("%s\n", "Blocks aren't aligned");
        return false;
    }
    if (!check_header_footer()) {
        printf("%s\n", "Header and footer don't match");
        return false;
    }
    if (!check_consec_free()) {
        printf("%s\n",
               "There are consecutive free blocks. Make sure coelescing.");
        return false;
    }
    if (!check_free_pointers()) {
        printf("%s\n", "Free pointers aren't consistent/mirrored");
        return false;
    }
    if (!check_free_location()) {
        printf("%s\n", "Free list pointers are out of bounds");
        return false;
    }
    if (!check_free_count()) {
        printf("%s\n", "Free list pointers don't match heap");
        return false;
    }
    if (!check_correct_bucket()) {
        printf("%s\n",
               "Some free blocks are not within their corresponding size");
        return false;
    }
    return true;
}

/**
 * @brief
 *
 * This function initiliazes the simulator/heap and is called
 * every time new trace file is used or restarting a trace file.
 * Resets the global variables so no data is being propogated through
 * different files.
 *
 * @return false if error in initiliazing
 */
bool mm_init(void) {
    heap_start = NULL;
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));
    for (size_t i = 0; i < segLength; i++) {
        segFreeLists[i] = NULL;
    }
    if (start == (void *)-1) {
        return false;
    }
    miniFreeList = NULL;

    start[0] = pack(0, true, true, true, true); // Heap prologue (block footer)
    start[1] = pack(0, true, true, true, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }
    return true;
}

/**
 * @brief
 *
 * This function allocates a block of given size
 *
 * @param[in] size of block to be allocated
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = max(min_block_size, round_up(size + wsize, dsize));

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    if (block_size > min_block_size) {
        write_block(block, block_size, true, true, false, get_prev_mini(block));
    } else {
        write_block(block, block_size, true, true, true, get_prev_mini(block));
    }

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * This function frees the block pointed to by bp.
 *
 * @param[in] bp. frees the block pointed to by this pointer
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    if (size > min_block_size) {
        write_block(block, size, false, get_prev_alloc(block), false,
                    get_prev_mini(block));
    } else {
        write_block(block, size, false, get_prev_alloc(block), true,
                    get_prev_mini(block));
    }

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * This function returns a pointer to an allocated region of at least size bytes
 * Constraints: if ptr is NULL, same as malloc(size)
 *              if size == 0, same as free(ptr) and return NULL
 *              if ptr != NULL, same as free(ptr) and then malloc(size), but
 * contents of this new block will be same as old block, up to min of old and
 * new sizes
 *
 * @param[in] ptr as mentioned above
 * @param[in] size as mentioned above
 * @return as mentioned above
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * this function allocates memory for an array of elements number of
 * elements of size each and returns a pointer to the allocated memory.
 * Memory is set to 0 before returning
 *
 * @param[in] elements # of elements to be allocated
 * @param[in] size of each element
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 71 6d 41 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 30 84 19 45 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 45 27 40 64 81 1e 4d 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
