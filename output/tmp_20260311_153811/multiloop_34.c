int main(int n) {
  /*@ requires -46340 <= n <= 46340; */
  if (n < 0) n = 0;
  int i, j;
  int diff = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant 0 <= diff;
      loop assigns i, j, diff;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    /*@ loop invariant 0 <= j <= i + 1;
        loop invariant 0 <= diff;
        loop assigns j, diff;
        loop variant i + 1 - j;
    */
    for (j = 0; j <= i; ++j) {
      diff += i - j;
    }
  }
  /*@ assert 0 <= diff; */
  return diff;
}
