#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* Beginning of generated code */

struct feverScore_mem
{ void (* dead);
};
struct main_mem
{ double d;
  struct feverScore_mem * obj_d;
};
double case_of_e(double __SCRUT__, double b);

void (feverScore_reset(struct feverScore_mem (* self))) {
  (void)(0);
}

double (feverScore_step(struct feverScore_mem (* self), double b)) {
  return (case_of_e)((b), (b));
}

void (main_reset(struct main_mem (* self))) {
  (feverScore_reset)(((*(self)).obj_d));
  ((*(self)).d) = (33.0);
}

double (main_step(struct main_mem (* self))) {
  double c;
  double a;
  (a) = ((*(self)).d);
  (c) = ((feverScore_step)(((*(self)).obj_d), (a)));
  ((*(self)).d) = ((1.0) + (a));
  return c;
}

double case_of_e(double __SCRUT__, double b) {
  if ((__SCRUT__) > (41.0)) {
    return (b) * (3000.0);
  };
  if ((__SCRUT__) > (37.5)) {
    return b;
  };
  if (1) {
    return 0.0;
  };
}

/* End of generated code */

int main (){
  struct main_mem *obj_main = malloc (sizeof(struct main_mem));
  struct feverScore_mem *obj_feverScore = malloc(sizeof(struct feverScore_mem));
  obj_main->obj_d = obj_feverScore;

  main_reset(obj_main);
  while(1){
    double x = main_step(obj_main);
    printf("%f\n",x);
    sleep(1);
  }
  return 0;
}
