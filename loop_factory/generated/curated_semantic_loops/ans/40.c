int main(int n) {
  if (n < 0) n = 0;
  int i = 0, j;
  int budget = n * (n + 1);
  /*@ loop invariant 0 <= i <= n;
      loop invariant budget == n * (n + 1) - i * (i + 1);
      loop assigns i, j, budget;
      loop variant n - i;
  */
  while (i < n) {
    /*@ loop invariant 0 <= j <= i;
        loop invariant budget == n * (n + 1) - i * (i + 1) - 2 * j;
        loop assigns j, budget;
        loop variant i - j;
    */
    for (j = 0; j < i; ++j) {
      budget -= 2;
    }
    budget -= 2;
    i++;
  }
  /*@ assert budget == 0 && budget % 2 == 0; */
  return budget;
}
