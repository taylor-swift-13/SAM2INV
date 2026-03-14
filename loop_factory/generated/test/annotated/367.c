int main1(){
  int rj, xz, y2a, ek56, eih, yb;
  rj=1*2;
  xz=0;
  y2a=0;
  ek56=0;
  eih=(1%18)+5;
  yb=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ek56 == xz;
  loop invariant xz == y2a;
  loop invariant yb == y2a*(y2a+1)/2;
  loop invariant (eih + y2a) == 6;
  loop invariant (0 <= y2a);
  loop invariant (y2a <= 6);
  loop assigns eih, xz, y2a, ek56, yb;
*/
while (eih>0) {
      eih = (eih)+(-(1));
      xz = xz+1*1;
      y2a = y2a+1*1;
      ek56 = ek56+1*1;
      yb += y2a;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ek56 <= 6;
  loop invariant rj >= 2;
  loop invariant yb >= 21;
  loop invariant ek56 > 0;
  loop assigns ek56, rj, yb;
*/
while (ek56>rj) {
      ek56 -= rj;
      rj++;
      yb = yb+(ek56%5);
      yb = yb*2;
  }
}