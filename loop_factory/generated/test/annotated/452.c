int main1(int k,int p){
  int xw, s4, qo3d, m;
  xw=p-7;
  s4=xw;
  qo3d=xw;
  m=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s4 >= (\at(p,Pre) - 7);
  loop invariant qo3d == (\at(p,Pre) - 7);
  loop assigns m, s4;
*/
while (s4-3>=0) {
      m = m+qo3d*s4;
      s4 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qo3d == (\at(p,Pre) - 7) + k * ( xw - (\at(p,Pre) - 7) );
  loop invariant xw <= s4;
  loop invariant xw >= (\at(p, Pre) - 7);
  loop assigns qo3d, xw;
*/
while (xw<s4) {
      qo3d = qo3d + k;
      xw += 1;
  }
}