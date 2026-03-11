int main(int n) {
  /*@ requires -46340 <= n <= 46340; */
  if (n < 0) n = 0;
  int i = 0, j;
  int z = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant z == 2 * i * (i - 1);
      loop assigns i, j, z;
      loop variant n - i;
  */
  while (i < n) {
    /*@ loop invariant 0 <= j <= i;
        loop invariant z == 2 * i * (i - 1) + 2 * j;
        loop assigns j, z;
        loop variant i - j;
    */
    for (j = 0; j < i; ++j) {
      z += 2;
    }
    z += 2 * i;
    i++;
  }
  /*@ assert z % 2 == 0 && z == 2 * n * (n - 1); */
  return z;
}
