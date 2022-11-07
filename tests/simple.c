#include <stdio.h>

int main() {
  int a, b, c, d;
  a = 42;
  b = a;
  c = a + b;
  if (a > 2) {
    c = 3;
  }
  a = c + 23;
  // c = a + d;
	return 0;
}
