#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* Beginning of generated code */

struct main_mem
{ int g;
  int f;
  int e;
};

void (main_reset(struct main_mem (* self))) {
  ((*(self)).g) = (0);
  ((*(self)).f) = (1);
  ((*(self)).e) = (0);
}

int (main_step(struct main_mem (* self))) {
  int c;
  int b;
  int d;
  int a;
  (c) = ((*(self)).g);
  (b) = ((*(self)).f);
  ((*(self)).g) = (b);
  ((*(self)).f) = (c);
  (a) = ((*(self)).e);
  switch (b) {
    case (1): (d) = (a); break;
    case (0): (void)(0); break;
  };
  ((*(self)).e) = ((1) + (a));
  return d;
}

/* End of generated code */


int main (){
  struct main_mem *obj_main = malloc (sizeof(struct main_mem));
  main_reset(obj_main);
  while(1){
    int x = main_step(obj_main);
    printf("%d\n",x);
    sleep(1);
  }
  return 0;
}
