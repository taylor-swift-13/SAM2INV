int main(int n) {
  /*@ requires 0 <= n <= 100; */
  if (n < 0) n = 0;
  int i, j;
  int even = 0;
  
  for (i = 0; i < n; ++i) {
    
    for (j = 0; j < n; ++j) {
      if (((i + j) % 2) == 0) even += 1;
    }
  }
  /*@ assert i == n; */
  return even;
}
