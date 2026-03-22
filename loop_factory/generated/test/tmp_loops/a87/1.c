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
