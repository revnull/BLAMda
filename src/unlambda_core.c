
#include <stdlib.h>
#include <stdio.h>
#include <alloca.h>
#include <sys/mman.h>
#include <ucontext.h>


typedef struct f {
    struct f *moved;
    int age;
    void (*fn)(struct f*, struct f*, struct f*);
    int size;
    struct f *d[];
} f;

ucontext_t trampoline;
ucontext_t ucp;
void *call_stack = NULL;
f *temp_self = NULL;
f *temp_input = NULL;
f *temp_cont = NULL;
void (*temp_fn)(struct f*, struct f*, struct f*);

int allocations;

#define PSTACK_SIZE 16000000
#define OLD_AGE 10

#define ALLOC_F(v,b) f* v = alloca(sizeof(f) + (b) * sizeof(f*));allocations++;v->moved=0;v->age=0;v->size=(b);
#define CHECK(fn) if ((((void *)&x) - call_stack) < 1024) {\
        temp_self = x;temp_input = y;temp_cont = z;temp_fn = fn;\
        setcontext(&trampoline);}

f root = { (f *) 0xbadbadbad, 0, 0, 0 };

f d = { &root, 0, NULL, 0 };

//f t = { &root, 0, NULL, 1, { &d }};

void apply(f *self, f *null, f *cont);

void exit_c(f *self, f *input, f *cont) {
      exit(0);
}

void eval(f *input, f *cont) {
    if ((((void *)&input) - call_stack) < 0) {
        fprintf(stderr, "TOO FAR!\n");
    }
    if ((((void *)&input) - call_stack) < 4096) {
        temp_self = NULL;
        temp_input = input;
        temp_cont = cont;
        temp_fn = NULL;
        setcontext(&trampoline);
    }

    if (input->fn == &apply) {
        input->fn(input,NULL,cont);
    } else {
        cont->fn(cont,input,NULL);
    }
}

void cc(f *self, f *input, f *null) {
    self->d[0]->fn(self->d[0], input, NULL);
}

void call_cc(f *self, f *input, f *cont) {
    ALLOC_F(c,1);
    c->d[0]=cont;
    c->fn=cc;
    input->fn(input, c, cont);
}

void d0k2(f *self, f *input, f *cont) {
    input->fn(input, self->d[0], self->d[1]);
}

void d0k1(f *self, f *input, f *cont) {
    ALLOC_F(c, 2)
    c->fn = d0k2;
    c->d[0] = input;
    c->d[1] = self->d[1];

    eval(self->d[0], c);
}

void d0(f *self, f *input, f *cont) {
    ALLOC_F(c, 2)
    c->fn = d0k1;
    c->d[0] = self->d[0];
    c->d[1] = cont;
    eval(input, c);
}

void applyk2(f *self, f *input, f *cont) {
    self->d[0]->fn(self->d[0], input, self->d[1]);
}

void applyk1(f *self, f *input, f *cont) {
    if (input == &d) {
        ALLOC_F(r, 1);
        r->fn = d0;
        r->d[0] = self->d[0];
        self->d[1]->fn(self->d[1], r, NULL);
    } else {
        ALLOC_F(c, 2);
        c->fn = applyk2;
        c->d[0] = input;
        c->d[1] = self->d[1];
        eval(self->d[0], c);
    }
}

void apply(f *self, f *null, f *cont) {
    ALLOC_F(c, 2)
    c->fn = applyk1;
    c->d[0] = self->d[1];
    c->d[1] = cont;
    eval(self->d[0], c);
}


void compose(f *self, f *input, f *cont) {
    if (cont) {
        ALLOC_F(c, 2)
        c->fn = compose;
        c->d[0] = self->d[1];
        c->d[1] = cont;
        self->d[0]->fn(self->d[0], input, c);
    } else {
        self->d[0]->fn(self->d[0], input, self->d[1]);
    }
}

f ex = { &root, 0, exit_c, 0 };
f callcc = { &root, 0, call_cc, 0 };

f* stacks[PSTACK_SIZE / sizeof(f)];

void *bases[2];
int current = 0;
char *permanent, *old_top;

void initialize (f *input, f *cont) {
    void *new_stack, *top;
    f *c;
    f *sp;
    int i;

    for(i=0; i<2; i++) {
        bases[i] = mmap(NULL, PSTACK_SIZE,
            PROT_READ|PROT_WRITE|PROT_EXEC,
            MAP_PRIVATE|MAP_ANONYMOUS|MAP_STACK, 0, 0);
    }

    permanent = mmap(NULL, PSTACK_SIZE,
        PROT_READ|PROT_WRITE,
        MAP_PRIVATE|MAP_ANONYMOUS, 0, 0);
    old_top = permanent + PSTACK_SIZE;

    getcontext(&trampoline);
    getcontext(&ucp);

    if (call_stack) {
        int st = 0;
        
        current = (current + 1) & 1;
        new_stack = bases[current];
       
        top = new_stack + PSTACK_SIZE;

        if (temp_self) stacks[st++] = temp_self;
        if (temp_input) stacks[st++] = temp_input;
        if (temp_cont) stacks[st++] = temp_cont;


        while(st) {
            sp = stacks[st-1];

            if (sp->moved == &root) {
                st--;
                continue;
            }
            if (sp->moved) {
                for(i=0; i<sp->size; i++) {
                    if(!sp->d[i]) {
                        sp->moved->d[i] = NULL;
                        continue;
                    }
                    if(!sp->d[i]->moved) break;
                    if(sp->d[i]->moved == &root) {
                        sp->moved->d[i] = sp->d[i];
                    } else {
                        sp->moved->d[i] = sp->d[i]->moved;
                    }
                }
                st--;
            } else {
                if (sp->age >= OLD_AGE) {
                    c = (f *)(((char *)old_top) - (sizeof(f) +
                                    sp->size * sizeof(f*)));
                    if ((char *) c < permanent) {
                        permanent = mmap(NULL, PSTACK_SIZE,
                            PROT_READ|PROT_WRITE,
                            MAP_PRIVATE|MAP_ANONYMOUS, 0, 0);
                        old_top = permanent + PSTACK_SIZE;
                        c = (f *)(((char *)old_top) - (sizeof(f) +
                                        sp->size * sizeof(f*)));
                    }
                    c->moved = &root;
                    old_top = (char*) c;
                } else {
                    c = (f *)(((char *)top) - (sizeof(f) +
                                    sp->size * sizeof(f*)));
                    top = (void*) c;
                    c->moved = 0;
                }
                sp->moved = c;
                c->size = sp->size;
                c->fn = sp->fn;
                c->age = sp->age + 1;
                for(i=0; i<sp->size; i++) {
                    if (sp->d[i] && !sp->d[i]->moved)
                        stacks[st++] = sp->d[i];
                }
            }

        }

        if (temp_self && temp_self->moved != &root) {
            temp_self = temp_self->moved;
        }
        if (temp_input && temp_input->moved != &root) {
            temp_input = temp_input->moved;
        }
        if (temp_cont && temp_cont->moved != &root) {
            temp_cont = temp_cont->moved;
        }
        ucp.uc_stack.ss_sp = new_stack;
        ucp.uc_stack.ss_size = top - new_stack;
        call_stack = new_stack;

        if (!temp_fn) {
            makecontext(&ucp, (void (*)(void))eval, 2, temp_input, temp_cont);
        } else {
            makecontext(&ucp, (void (*)(void))temp_fn, 3, temp_self, temp_input, temp_cont);
        }
    } else {
        ucp.uc_stack.ss_sp = call_stack = bases[0];
        ucp.uc_stack.ss_size = PSTACK_SIZE;
        ucp.uc_link = NULL;

        makecontext(&ucp, (void (*)(void))eval, 2, input, cont);
    }

    allocations = 0;
    setcontext(&ucp);
}

