int main1(int o,int d){
  int r8, gxk, r3t, r, j8n, p, gauc, bp, c9;
  r8=d-3;
  gxk=r8;
  r3t=r8;
  r=gxk;
  j8n=-5;
  p=3;
  gauc=0;
  bp=6;
  c9=gxk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r + r3t == gxk + (\at(d, Pre) - 3);
  loop invariant j8n >= -5;
  loop invariant o - \at(o,Pre) == 3*(p - 3);
  loop invariant d - \at(d,Pre) == bp - 6;
  loop invariant 0 <= p - 3;
  loop invariant r8 == \at(d, Pre) - 3;
  loop invariant gxk - p == \at(d,Pre) - 6;
  loop invariant gauc == 0;
  loop invariant r <= gxk;
  loop invariant r3t <= gxk;
  loop assigns r3t, r, j8n, bp, d, o, p, c9, gxk;
*/
while (gxk-3>=0) {
      if (gxk%5==0) {
          r3t += 1;
      }
      else {
          r = r + 1;
      }
      if (gxk%5==1) {
          j8n += 1;
      }
      else {
      }
      bp += j8n;
      d += j8n;
      o = o + 3;
      p++;
      c9 = p+gauc+bp;
      gxk = gxk + 1;
  }
}