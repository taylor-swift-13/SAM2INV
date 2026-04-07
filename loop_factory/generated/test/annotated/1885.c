int main1(){
  int y, mi0, n, ky, xh2, acof, muw, f5, q, sp69, pdl6;
  y=1*5;
  mi0=0;
  n=y;
  ky=-8;
  xh2=y;
  acof=y;
  muw=mi0;
  f5=0;
  q=1*3;
  sp69=y;
  pdl6=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == (5 + mi0*(mi0 - 1)/2) % 256;
  loop invariant muw == 0;
  loop invariant y == 5;
  loop invariant 0 <= mi0 <= y;
  loop invariant -96 <= ky;
  loop invariant ky <= 96;
  loop invariant 0 <= q <= 22;
  loop invariant 0 <= sp69 <= 28;
  loop invariant 0 <= pdl6 <= 30;
  loop invariant 0 <= xh2 <= 63;
  loop invariant 0 <= acof <= 12;
  loop invariant 0 <= f5 <= 18;
  loop assigns n, ky, f5, xh2, acof, q, sp69, pdl6, mi0, muw;
*/
while (1) {
      if (!(mi0 < y)) {
          break;
      }
      n = (n + mi0) % 256;
      ky = (ky + xh2) % 97;
      f5 = (f5 + q) % 19;
      xh2 = (xh2 + pdl6) % 64;
      acof = (acof + muw) % 13;
      q = (q + sp69) % 23;
      sp69 = (sp69 + pdl6) % 29;
      pdl6 = (pdl6 + 1) % 31;
      mi0++;
      if (!(!((mi0%2)==0))) {
          muw += 2;
      }
      if (mi0<q+1) {
          muw = muw + muw;
      }
      muw = muw - muw;
  }
}