int main(int n) {
  /*@ requires 0 <= n <= 100; */
  if (n < 0) n = 0;
  int i = 0, j;
  int z = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant z % 2 == 0;
      loop invariant 0 <= z;
      loop assigns i, j, z;
      loop variant n - i;
  */
  while (i < n) {
    /*@ loop invariant 0 <= j <= i;
        loop invariant z % 2 == 0;
        loop invariant 0 <= z;
        loop assigns j, z;
        loop variant i - j;
    */
    for (j = 0; j < i; ++j) {
      z += 2;
    }
    z += 2 * i;
    i++;
  }
  /*@ assert i == n && z % 2 == 0 && z >= 0; */
  return z;
}
