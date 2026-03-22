int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int bands = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant i * n <= bands <= 2 * i * n;
      loop assigns i, j, bands;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    j = 0;
    /*@ loop invariant 0 <= j <= n;
        loop invariant i * n + j <= bands <= 2 * i * n + 2 * j;
        loop assigns j, bands;
        loop variant n - j;
    */
    while (j < n) {
      if (j <= i / 2) bands += 2;
      else bands += 1;
      j++;
    }
  }
  /*@ assert (n == 0 || bands >= n * n) && bands <= 2 * n * n; */
  return bands;
}
