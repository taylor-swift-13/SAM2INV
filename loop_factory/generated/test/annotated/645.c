int main1(int o){
  int mfi, xo, n7, t57, jb;
  mfi=o;
  xo=mfi;
  n7=0;
  t57=o;
  jb=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mfi == \at(o, Pre);
  loop invariant t57 == mfi - n7;
  loop invariant jb == 7 + n7*(n7 + 1)/2;
  loop invariant 0 <= n7;
  loop invariant mfi == o;
  loop assigns n7, t57, jb;
*/
while (1) {
      if (!(n7<mfi)) {
          break;
      }
      n7 = n7 + 1;
      t57 = mfi-n7;
      jb = jb + n7;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mfi <= xo;
  loop invariant xo == o;
  loop invariant mfi >= o;
  loop invariant xo == \at(o, Pre);
  loop assigns mfi;
*/
while (mfi<xo) {
      mfi++;
  }
}