#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* Beginning of generated code */

struct main_mem
{ int b;
};

void (main_reset(struct main_mem (* self))) {
  ((*(self)).b) = (0);
}

int (main_step(struct main_mem (* self))) {
  int a;
  (a) = ((*(self)).b);
  ((*(self)).b) = ((1) + (a));
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
