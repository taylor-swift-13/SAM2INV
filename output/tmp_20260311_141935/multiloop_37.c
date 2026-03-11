int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int slots = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant 0 <= slots <= n * (n + 1) / 2;
      loop assigns i, j, slots;
      loop variant i;
  */
  for (i = n; i > 0; --i) {
    /*@ loop invariant -1 <= j <= i;
        loop assigns j, slots;
        loop variant j + 1;
    */
    for (j = i - 1; j >= 0; j -= 2) {
      slots += 1;
    }
  }
  /*@ assert (n == 0 || slots >= n / 2) && slots <= n * (n + 1) / 2; */
  return slots;
}
