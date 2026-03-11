int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int budget = n * n;
  /*@ loop invariant 0 <= i <= n;
      loop invariant budget >= 0;
      loop assigns i, j, budget;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    /*@ loop invariant 0 <= j <= i;
        loop invariant budget == n * n - (i * (i - 1)) / 2 - j;
        loop assigns j, budget;
        loop variant i - j;
    */
    for (j = 0; j < i; ++j) {
      budget -= 1;
    }
  }
  /*@ assert budget == n * (n + 1) / 2; */
  return budget;
}
