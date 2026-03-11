int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int diff = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant diff == i * (i - 1) * (i + 1) / 6;
      loop assigns i, j, diff;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    /*@ loop invariant 0 <= j <= i + 1;
        loop invariant diff == i * (i - 1) * (i + 1) / 6 + (j * (2 * i - j + 1)) / 2;
        loop assigns j, diff;
        loop variant i + 1 - j;
    */
    for (j = 0; j <= i; ++j) {
      diff += i - j;
    }
  }
  /*@ assert diff == n * (n - 1) * (n + 1) / 6; */
  return diff;
}
