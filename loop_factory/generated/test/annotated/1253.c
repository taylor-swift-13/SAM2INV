int main1(){
  int wge, jw, xb, bh, n7d, cu, pj;
  wge=1+12;
  jw=0;
  xb=1;
  bh=4;
  n7d=16;
  cu=wge;
  pj=jw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bh == 4 + ((xb - 1) * xb * (2 * xb - 1)) / 6;
  loop invariant pj == (wge - jw) * (xb - 1);
  loop invariant pj == (xb - 1) * wge;
  loop invariant 1 <= xb;
  loop invariant xb <= wge + 1;
  loop invariant n7d >= 16;
  loop invariant cu >= 13;
  loop assigns bh, xb, n7d, pj, cu;
*/
while (1) {
      if (!(xb<=wge)) {
          break;
      }
      bh = bh+xb*xb;
      xb += 1;
      n7d = n7d+(xb%8);
      pj = pj+wge-jw;
      cu = cu+(bh%5);
      n7d = n7d*3+5;
      cu = cu*n7d+5;
  }
}