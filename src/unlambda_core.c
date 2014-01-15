
#include <stdlib.h>
#include <stdio.h>
#include <alloca.h>
#include <sys/mman.h>
#include <ucontext.h>


typedef struct closure {
    struct closure *moved;
    int age;
    void (*fn)(struct closure*, struct closure*, struct closure*);
    int size;
    struct closure *data[];
} closure;

ucontext_t trampoline;
ucontext_t ucp;
void *call_stack = NULL;
closure *temp_self = NULL;
closure *temp_input = NULL;
closure *temp_cont = NULL;
void (*temp_fn)(struct closure*, struct closure*, struct closure*);

int allocations;

#define PSTACK_SIZE 16000000
#define OLD_AGE 10

#define ALLOC_F(v,b) closure* v = alloca(sizeof(closure) + (b) * sizeof(closure*));allocations++;v->moved=0;v->age=0;v->size=(b);
#define CHECK(fn) if ((((void *)&input) - call_stack) < 4096) {\
        temp_self = self;temp_input = input;temp_cont = cont;temp_fn = fn;\
        setcontext(&trampoline);}

closure root = { (closure *) 0xbadbadbad, 0, 0, 0 };

closure d = { &root, 0, NULL, 0 };

//closure t = { &root, 0, NULL, 1, { &d }};

void apply(closure *self, closure *null, closure *cont);

void exit_c(closure *self, closure *input, closure *cont) {
      exit(0);
}

void eval(closure *input, closure *cont) {
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

void cc(closure *self, closure *input, closure *null) {
    self->data[0]->fn(self->data[0], input, NULL);
}

void call_cc(closure *self, closure *input, closure *cont) {
    ALLOC_F(c,1);
    c->data[0]=cont;
    c->fn=cc;
    input->fn(input, c, cont);
}

void d0k2(closure *self, closure *input, closure *cont) {
    input->fn(input, self->data[0], self->data[1]);
}

void d0k1(closure *self, closure *input, closure *cont) {
    ALLOC_F(c, 2)
    c->fn = d0k2;
    c->data[0] = input;
    c->data[1] = self->data[1];

    eval(self->data[0], c);
}

void d0(closure *self, closure *input, closure *cont) {
    ALLOC_F(c, 2)
    c->fn = d0k1;
    c->data[0] = self->data[0];
    c->data[1] = cont;
    eval(input, c);
}

void applyk2(closure *self, closure *input, closure *cont) {
    self->data[0]->fn(self->data[0], input, self->data[1]);
}

void applyk1(closure *self, closure *input, closure *cont) {
    if (input == &d) {
        ALLOC_F(r, 1);
        r->fn = d0;
        r->data[0] = self->data[0];
        self->data[1]->fn(self->data[1], r, NULL);
    } else {
        ALLOC_F(c, 2);
        c->fn = applyk2;
        c->data[0] = input;
        c->data[1] = self->data[1];
        eval(self->data[0], c);
    }
}

void apply(closure *self, closure *null, closure *cont) {
    ALLOC_F(c, 2)
    c->fn = applyk1;
    c->data[0] = self->data[1];
    c->data[1] = cont;
    eval(self->data[0], c);
}


void compose(closure *self, closure *input, closure *cont) {
    if (cont) {
        ALLOC_F(c, 2)
        c->fn = compose;
        c->data[0] = self->data[1];
        c->data[1] = cont;
        self->data[0]->fn(self->data[0], input, c);
    } else {
        self->data[0]->fn(self->data[0], input, self->data[1]);
    }
}

closure ex = { &root, 0, exit_c, 0 };
closure callcc = { &root, 0, call_cc, 0 };

closure* stacks[PSTACK_SIZE / sizeof(closure)];

void *bases[2];
int current = 0;
char *permanent, *old_top;

void initialize (closure *input, closure *cont) {
    void *new_stack, *top;
    closure *c;
    closure *sp;
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
                    if(!sp->data[i]) {
                        sp->moved->data[i] = NULL;
                        continue;
                    }
                    if(!sp->data[i]->moved) break;
                    if(sp->data[i]->moved == &root) {
                        sp->moved->data[i] = sp->data[i];
                    } else {
                        sp->moved->data[i] = sp->data[i]->moved;
                    }
                }
                st--;
            } else {
                if (sp->age >= OLD_AGE) {
                    c = (closure *)(((char *)old_top) - (sizeof(closure) +
                                    sp->size * sizeof(closure*)));
                    if ((char *) c < permanent) {
                        permanent = mmap(NULL, PSTACK_SIZE,
                            PROT_READ|PROT_WRITE,
                            MAP_PRIVATE|MAP_ANONYMOUS, 0, 0);
                        old_top = permanent + PSTACK_SIZE;
                        c = (closure *)(((char *)old_top) - (sizeof(closure) +
                                        sp->size * sizeof(closure*)));
                    }
                    c->moved = &root;
                    old_top = (char*) c;
                } else {
                    c = (closure *)(((char *)top) - (sizeof(closure) +
                                    sp->size * sizeof(closure*)));
                    top = (void*) c;
                    c->moved = 0;
                }
                sp->moved = c;
                c->size = sp->size;
                c->fn = sp->fn;
                c->age = sp->age + 1;
                for(i=0; i<sp->size; i++) {
                    if (sp->data[i] && !sp->data[i]->moved)
                        stacks[st++] = sp->data[i];
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

