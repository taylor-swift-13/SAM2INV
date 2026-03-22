int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int s = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant s == i * (i + 1) / 2;
      loop assigns i, j, s;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    /*@ loop invariant 0 <= j <= i + 1;
        loop invariant s == i * (i + 1) / 2 + j;
        loop assigns j, s;
        loop variant i + 1 - j;
    */
    for (j = 0; j <= i; ++j) {
      s += 1;
    }
  }
  /*@ assert s == n * (n + 1) / 2; */
  return s;
}
