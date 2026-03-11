int main(int n) {
  /*@ requires 0 <= n <= 100; */
  if (n < 0) n = 0;
  int i = 0, j;
  int cells = 0;
  int odd_hits = 0;
/*@ loop invariant 0 <= i <= n;
      loop invariant 0 <= cells;
      loop invariant 0 <= odd_hits;
      loop assigns i, j, cells, odd_hits;
      loop variant n - i;
  */
  while (i < n) {
    j = 0;
    /*@ loop invariant 0 <= j <= n;
        loop invariant 0 <= cells;
        loop invariant 0 <= odd_hits;
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
  /*@ assert cells >= 0 && odd_hits >= 0; */
  return cells + odd_hits;
}
