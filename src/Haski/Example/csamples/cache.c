#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdbool.h>

/*
* NOTE: The unnecessary `if (true)` blocks below are a hack used to sequence statements
* since the current C library doesn't support statement blocks inside switch statements.
* Although this is an ugly technicality which can be remedied by fixing the 
* library or changing it, we leave the code as it is for the time being, 
* and let the (GCC/Clang) optimizer to discard these unecessary conditionals statements.
*/

/* Beginning of generated code */

struct cache_mem
{ int i;
};
struct main_mem
{ unsigned short i;
  unsigned short h;
  struct cache_mem * obj_h;
};

void (cache_reset(struct cache_mem (* self))) {
  ((*(self)).i) = (0);
}

unsigned short (cache_step(struct cache_mem (* self), unsigned short c)) {
  int h;
  int e;
  int d;
  unsigned short k;
  unsigned short j;
  unsigned short f;
  (e) = ((*(self)).i);
  switch (c) {
    case (2): if (true) {
                (h) = (1);
                break;
              };
    case (1): if (true) {
                (h) = (0);
                break;
              };
    case (0): if (true) {
                (h) = (e);
                break;
              };
  };
  (d) = (h);
  switch (d) {
    case (1): if (true) {
                (j) = (2);
                break;
              };
    case (0): if (true) {
                (j) = (1);
                break;
              };
  };
  switch (c) {
    case (2): if (true) {
                (k) = (0);
                break;
              };
    case (1): if (true) {
                (k) = (0);
                break;
              };
    case (0): if (true) {
                (k) = (j);
                break;
              };
  };
  (f) = (k);
  ((*(self)).i) = (d);
  return f;
}

void (main_reset(struct main_mem (* self))) {
  (cache_reset)(((*(self)).obj_h));
  ((*(self)).i) = (0);
  ((*(self)).h) = (2);
}

unsigned short (main_step(struct main_mem (* self))) {
  unsigned short b;
  unsigned short a;
  unsigned short g;
  (b) = ((*(self)).i);
  (a) = ((*(self)).h);
  (g) = ((cache_step)(((*(self)).obj_h), (a)));
  ((*(self)).i) = (a);
  ((*(self)).h) = (b);
  return g;
}

/* End of generated code */


int main (){

  struct main_mem *obj_main   = malloc (sizeof(struct main_mem));
  struct cache_mem *obj_cache = malloc (sizeof(struct cache_mem));

  obj_main->obj_h = obj_cache;
  main_reset(obj_main);

  while(1) {
    int x = main_step(obj_main);
    printf("%d\n",x);
    sleep(1);
  }

  return 0;
}

