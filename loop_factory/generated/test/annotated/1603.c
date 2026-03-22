int main1(){
  int uvp, dg, gm2, hex, of, wj, wu, l3h, qh, ix, uc6;
  uvp=(1%8)+15;
  dg=0;
  gm2=1;
  hex=1;
  of=0;
  wj=5;
  wu=0;
  l3h=dg;
  qh=8;
  ix=dg;
  uc6=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dg == wu;
  loop invariant 0 <= dg;
  loop invariant dg <= uvp;
  loop invariant 0 <= gm2;
  loop invariant gm2 <= wj;
  loop invariant (gm2 + of - hex) == 0;
  loop invariant of >= 0;
  loop invariant uc6 == -8;
  loop invariant uvp == 16;
  loop invariant wj == 5;
  loop invariant l3h >= 8 * dg;
  loop invariant of <= dg;
  loop invariant 1 <= hex;
  loop invariant hex <= 1 + dg;
  loop invariant ix == dg * uc6 + (dg + 1) / 2;
  loop invariant qh == 8 + dg * wj + (dg + 1) / 2;
  loop assigns dg, gm2, of, hex, wu, ix, qh, l3h;
*/
while (dg<uvp) {
      if (!(!(dg%3==0))) {
          if (gm2>0) {
              gm2 -= 1;
              of = of + 1;
          }
      }
      else {
          if (gm2<wj) {
              gm2++;
              hex++;
          }
      }
      wu += 1;
      dg += 1;
      ix = ix+(dg%2);
      qh = qh+(dg%2);
      l3h = l3h + qh;
      qh = qh + wj;
      ix += uc6;
  }
}