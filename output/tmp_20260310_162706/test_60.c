int main1(int g){
  int n, qt, m, xj;
  n=g+17;
  qt=0;
  m=0;
  xj=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (g - m) == \at(g, Pre) - qt;
  loop invariant m == (9*qt - qt*qt)/2;
  loop invariant n == \at(g, Pre) + 17;
  loop invariant xj + qt == 4;
  loop assigns g, m, qt, xj;
*/
while (qt<n&&xj>0) {
      qt++;
      m += xj;
      xj -= 1;
      g += xj;
  }
/*@
  assert !(qt<n&&xj>0) &&
         ((g - m) == \at(g, Pre) - qt);
*/

}