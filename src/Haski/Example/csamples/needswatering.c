#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* Beginning of generated code */

struct needsWatering_mem
{ void (* dead);
};
struct main_mem
{ int h;
  struct needsWatering_mem * obj_h;
};
int case_of_i(int __SCRUT__);
int case_of_k(double __SCRUT__);

void (needsWatering_reset(struct needsWatering_mem (* self))) {
  (void)(0);
}

int (needsWatering_step(struct needsWatering_mem (* self), double b, int c)) {
  return ((case_of_i)((c))) ? 1 : ((case_of_k)((b)));
}

void (main_reset(struct main_mem (* self))) {
  (needsWatering_reset)(((*(self)).obj_h));
  ((*(self)).h) = (0);
}

int (main_step(struct main_mem (* self))) {
  int a;
  int g;
  (a) = ((*(self)).h);
  (g) = ((needsWatering_step)(((*(self)).obj_h), (26.0), (a)));
  ((*(self)).h) = ((1) + (a));
  return g;
}

int case_of_i(int __SCRUT__) {
  if ((__SCRUT__) > (20)) {
    return 0;
  };
  if (1) {
    return 1;
  };
}

int case_of_k(double __SCRUT__) {
  int ErrorCode_0_d = (127);
  int ErrorCode_0_f = (1);
  if ((__SCRUT__) > (999.0)) {
    return (ErrorCode_0_d) > (126);
  };
  if ((__SCRUT__) > (38.0)) {
    return 1;
  };
  if ((__SCRUT__) > (5.0)) {
    return 0;
  };
  if (1) {
    return (ErrorCode_0_f) > (126);
  };
}

/* End of generated code */

int main (){
  struct main_mem *obj_main = malloc (sizeof(struct main_mem));
  struct needsWatering_mem *obj_needsWatering =
    malloc(sizeof(struct needsWatering_mem));
  obj_main->obj_h = obj_needsWatering;

  main_reset(obj_main);
  while(1){
    int x = main_step(obj_main);
    printf("%d\n",x);
    sleep(1);
  }
  return 0;
}
