
void* a;                // [mptr]                 === index ==>     [mref]
void** b;               // [mptr, mptr]           === index ==>     [mptr]
const void* c;          // [const, mptr]          === index ==>     [cref]
void *const d;          // [cptr]                 === index ==>     [cref]
void *const *const e;   // [cptr, cptr]           === index ==>     [cptr]
const void* const* f;   // [const, mptr, cptr]    === index ==>     [cptr]

struct X {
    int* a;                // [mptr]                 === index ==>     [mref]
    int** b;               // [mptr, mptr]           === index ==>     [mptr]
    const int* c;          // [const, mptr]          === index ==>     [cref]
    int *const d;          // [cptr]                 === index ==>     [cref]
    int *const *const e;   // [cptr, cptr]           === index ==>     [cptr]
    const int* const* f;   // [const, mptr, cptr]    === index ==>     [cptr]
};