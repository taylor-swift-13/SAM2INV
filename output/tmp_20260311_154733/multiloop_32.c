int main(int n) {
  /*@ requires -46340 <= n <= 46340; */
  if (n < 0) n = 0;
  int i = 0, j;
  int cells = 0;
  int odd_hits = 0;
/*@ loop invariant 0 <= i <= n;
      loop invariant cells == i * n;
      loop invariant 0 <= odd_hits <= cells;
      loop assigns i, j, cells, odd_hits;
      loop variant n - i;
  */
  while (i < n) {
    j = 0;
    /*@ loop invariant 0 <= j <= n;
        loop invariant cells == i * n + j;
        loop assigns j, cells, odd_hits;
        loop variant n - j;
    */
    while (j < n) {
      cells += 1;
      if (((i + j) % 2) != 0) odd_hits += 1;
      j++;
    }
    i++;
  }
  /*@ assert cells == n * n && 0 <= odd_hits <= cells; */
  return cells + odd_hits;
}
