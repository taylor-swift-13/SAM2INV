int main(int n) {
  /*@ requires 0 <= n <= 100; */
  if (n < 0) n = 0;
  int i = 0, j;
  int z = 0;
  
  while (i < n) {
    
    for (j = 0; j < i; ++j) {
      z += 2;
    }
    z += 2 * i;
    i++;
  }
  /*@ assert i == n; */
  return z;
}
