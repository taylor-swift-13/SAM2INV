int main(int n) {
  /*@ requires 0 <= n <= 100; */
  if (n < 0) n = 0;
  int i, j;
  int budget = n * n;
  /*@ loop invariant \true;
      loop assigns i, j, budget;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    /*@ loop invariant \true;
        loop assigns j, budget;
        loop variant i - j;
    */
    for (j = 0; j < i; ++j) {
      budget -= 1;
    }
  }
  /*@ assert i == n; */
  return budget;
}
