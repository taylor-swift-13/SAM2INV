int main1(int n){
  int qfv, m;
  qfv=(n%25)+13;
  m=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qfv == ((\at(n, Pre) % 25) + 13);
  loop invariant m >= 1;
  loop invariant (m % 2) == 1;
  loop invariant n >= \at(n, Pre) + m - 1;
  loop assigns m, n;
*/
while (m<=qfv) {
      m = m + m;
      m++;
      n = n + m;
  }
}