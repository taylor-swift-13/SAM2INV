int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int even = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant 0 <= even;
      loop assigns i, j, even;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    /*@ loop invariant 0 <= j <= n;
        loop assigns j, even;
        loop variant n - j;
    */
    for (j = 0; j < n; ++j) {
      if (((i + j) % 2) == 0) even += 1;
    }
  }
  /*@ assert 0 <= even <= n * n; */
  return even;
}
