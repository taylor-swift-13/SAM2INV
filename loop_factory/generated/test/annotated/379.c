int main1(int n){
  int m6, f52, xra;
  m6=n;
  f52=0;
  xra=m6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre) + f52 * m6 - (f52 * (f52 + 1)) / 2;
  loop invariant 0 <= f52;
  loop invariant m6 == \at(n, Pre);
  loop invariant n >= \at(n, Pre);
  loop invariant f52 + xra == m6;
  loop assigns n, f52, xra;
*/
while (f52<m6) {
      f52++;
      xra = m6-f52;
      n = n + xra;
  }
}