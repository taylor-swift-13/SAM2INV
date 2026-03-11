int main1(int c){
  int zp, c6, vt, x1;
  zp=c+12;
  c6=zp;
  vt=0;
  x1=c6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(c, Pre);
  loop invariant c6 == zp;
  loop invariant vt % 3 == 0;
  loop invariant vt >= 0;
  loop invariant zp == \at(c, Pre) + 12;
  loop assigns c, vt, x1;
*/
while (vt<zp) {
      x1 = zp-vt;
      c = c+zp-c6;
      vt = vt + 3;
  }
}