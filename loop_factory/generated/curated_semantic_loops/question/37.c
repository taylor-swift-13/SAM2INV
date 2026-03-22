int main(int n) {
  if (n < 0) n = 0;
  int i, j;
  int bands = 0;
  
  for (i = 0; i < n; ++i) {
    j = 0;
    
    while (j < n) {
      if (j <= i / 2) bands += 2;
      else bands += 1;
      j++;
    }
  }
  /*@ assert (n == 0 || bands >= n * n) && bands <= 2 * n * n; */
  return bands;
}
