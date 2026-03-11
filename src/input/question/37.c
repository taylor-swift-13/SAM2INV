int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int s = 0;
  
  for (i = 0; i < n; ++i) {
    
    for (j = 0; j <= i; ++j) {
      s += 1;
    }
  }
  /*@ assert s == n * (n + 1) / 2; */
  return s;
}
