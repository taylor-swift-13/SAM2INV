int main1(){
  int qx, y9, r1, ri, d, lrs;
  qx=79;
  y9=0;
  r1=-6;
  ri=y9;
  d=y9;
  lrs=y9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant -5*y9 <= ri <= 5*y9;
  loop invariant 0 <= y9;
  loop invariant y9 < qx;
  loop invariant d == 0;
  loop invariant lrs == 0;
  loop invariant r1 <= -6;
  loop invariant qx == 79;
  loop assigns ri, d, y9, r1;
*/
while (1) {
      ri = ((r1%6))+(ri);
      d = d+d+lrs;
      y9++;
      r1 = r1*4+4;
      if (y9>=qx) {
          break;
      }
  }
}