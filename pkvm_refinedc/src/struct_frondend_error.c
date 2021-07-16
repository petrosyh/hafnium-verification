#include <assert.h>

struct dummy {
  int a;
  int b;
};


struct dummy_wrapper {
  int wrapper_value;
  struct dummy dummy_value;
};



struct dummy_wrapper initialize_dummy(int a_value) {
  struct dummy_wrapper res = { .wrapper_value = 0, .dummy_value = {.a = a_value, .b = 0}};
  return res;
}


int main(void) {

  initialize_dummy(1);

  return 1;
}
