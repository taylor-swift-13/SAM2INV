int main(int n) {
  /*@ requires 0 <= n <= 100; */
  if (n < 0) n = 0;
  int i, j;
  int slots = 0;
  
  for (i = n; i > 0; --i) {
    
    for (j = i - 1; j >= 0; j -= 2) {
      slots += 1;
    }
  }
  /*@ assert i == 0; */
  return slots;
}
