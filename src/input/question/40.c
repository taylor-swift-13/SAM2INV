int main(int n) {
  /*@ requires 0 <= n <= 100; */
  if (n < 0) n = 0;
  int i, j;
  int diff = 0;
  
  for (i = 0; i < n; ++i) {
    
    for (j = 0; j <= i; ++j) {
      diff += i - j;
    }
  }
  /*@ assert i == n; */
  return diff;
}
