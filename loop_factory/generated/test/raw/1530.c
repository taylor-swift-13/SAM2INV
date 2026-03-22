int main1(){
  int wc, ij6, n, gn, w, xw, ppi, p8, phc;

  wc=1+8;
  ij6=0;
  n=-5;
  gn=0;
  w=0;
  xw=wc;
  ppi=20;
  p8=wc;
  phc=ij6;

  while (ij6 < wc) {
      if (ij6 < wc/2) {
          n += 1;
          gn = gn + 1;
      }
      if (ij6 >= wc/2) {
          w += 1;
          xw += 1;
      }
      else {
      }
      phc = phc + w;
      ij6++;
      ppi = ppi + 3;
      p8 = p8 + ppi;
      ppi += p8;
      phc += p8;
  }

}
