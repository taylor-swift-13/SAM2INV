int main1(){
  int xzb, qx, rg9, ur;
  xzb=(1%17)+12;
  qx=0;
  rg9=2;
  ur=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= qx;
  loop invariant qx <= xzb;
  loop invariant (ur == 1) || (ur == -1);
  loop invariant xzb == 13;
  loop invariant (rg9 - qx) <= 2;
  loop invariant 2 <= rg9 <= 11;
  loop assigns qx, rg9, ur;
*/
while (qx<xzb) {
      if (rg9>=11) {
          ur = -1;
      }
      if (!(rg9>2)) {
          ur = 1;
      }
      qx += 1;
      rg9 = rg9 + ur;
  }
}