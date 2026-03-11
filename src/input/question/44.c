int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int t = 0;
  
  for (i = 0; i < n; ++i) {
    
    for (j = 0; j < n; ++j) {
      t += 1;
    }
    t -= (n - 1);
  }
  /*@ assert t == n; */
  return t;
}
