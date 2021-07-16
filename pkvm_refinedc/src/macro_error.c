#include <assert.h>

#define __AC(X,Y)       (X##Y)
#define _AC(X,Y)        __AC(X,Y)
#define _UL(x)          (_AC(x, UL))
#define UL(x)           (_UL(x))

int main(void) {
 
  UL(10);

  return 0;
}
