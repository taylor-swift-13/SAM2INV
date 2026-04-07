int main1(){
  int cp, wh, j5, lyr, f6, sq, c, uc, pt, gcp;

  cp=1+15;
  wh=0;
  j5=2;
  lyr=wh;
  f6=cp;
  sq=20;
  c=wh;
  uc=cp;
  pt=cp;
  gcp=0;

  while (wh < cp) {
      c = wh % 4;
      if (c == 0) {
          gcp += 1;
      }
      else {
      }
      if (c == 1) {
          pt = pt + 1;
      }
      else {
      }
      if (c == 2) {
          uc = uc + 1;
      }
      else {
      }
      if (c == 3) {
          lyr++;
      }
      else {
      }
      f6 += pt;
      j5 += uc;
      wh++;
      f6 += sq;
      sq = sq + j5;
      j5 = (f6)+(j5);
      j5 += sq;
  }

}
