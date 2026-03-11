int main(int n) {
  /*@ requires 0 <= n <= 100; */
  if (n < 0) n = 0;
  int i, j;
  int slots = 0;
  /*@ loop invariant \true;
      loop assigns i, j, slots;
      loop variant i;
  */
  for (i = n; i > 0; --i) {
    /*@ loop invariant \true;
        loop assigns j, slots;
        loop variant j + 1;
    */
    for (j = i - 1; j >= 0; j -= 2) {
      slots += 1;
    }
  }
  /*@ assert i == 0 && slots >= 0; */
  return slots;
}
