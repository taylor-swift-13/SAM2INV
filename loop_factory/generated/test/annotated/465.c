int main1(int r,int a){
  int xb, zp, f, bkp;
  xb=r;
  zp=0;
  f=0;
  bkp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xb == \at(r, Pre);
  loop invariant r == \at(r, Pre) * (bkp + 1);
  loop invariant f == \at(r, Pre) * bkp * (bkp + 1) / 2;
  loop invariant zp == 0;
  loop invariant 0 <= bkp;
  loop invariant (xb > 0) ==> (0 <= bkp && bkp <= xb);
  loop assigns bkp, f, r;
*/
while (1) {
      if (!(bkp<xb)) {
          break;
      }
      bkp += 1;
      f += r;
      r = r+xb-zp;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(r, Pre) * (bkp + 1);
  loop invariant 0 <= bkp;
  loop invariant zp == (f - (\at(r, Pre) * bkp * (bkp + 1) / 2)) * ( \at(r, Pre) * (bkp + 1) + a );
  loop assigns zp, f;
*/
while (1) {
      zp = zp+r+a;
      f = f + 1;
      if (f>=bkp) {
          break;
      }
  }
}