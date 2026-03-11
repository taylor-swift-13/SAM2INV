int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int t = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant t == i;
      loop assigns i, j, t;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    /*@ loop invariant 0 <= j <= n;
        loop invariant t == i + j;
        loop assigns j, t;
        loop variant n - j;
    */
    for (j = 0; j < n; ++j) {
      t += 1;
    }
    t -= (n - 1);
  }
  /*@ assert t == n; */
  return t;
}
