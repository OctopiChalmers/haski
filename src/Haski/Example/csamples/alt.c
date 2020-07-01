#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* Beginning of generated code */

struct main_mem
{ int d;
  int c;
};

void (main_reset(struct main_mem (* self))) {
  ((*(self)).d) = (0);
  ((*(self)).c) = (1);
}

int (main_step(struct main_mem (* self))) {
  int b;
  int a;
  (b) = ((*(self)).d);
  (a) = ((*(self)).c);
  ((*(self)).d) = (a);
  ((*(self)).c) = (b);
  return a;
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
