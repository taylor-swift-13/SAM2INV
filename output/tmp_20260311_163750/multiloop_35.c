int main(int n) {
  /*@ requires 0 <= n <= 100; */
  if (n < 0) n = 0;
  int i, j;
  int even = 0;
  /*@ loop invariant even >= 0;
      loop assigns i, j, even;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    /*@ loop invariant even >= 0;
        loop assigns j, even;
        loop variant n - j;
    */
    for (j = 0; j < n; ++j) {
      if (((i + j) % 2) == 0) even += 1;
    }
  }
  /*@ assert i == n && even >= 0; */
  return even;
}
