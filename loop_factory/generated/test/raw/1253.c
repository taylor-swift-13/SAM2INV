int main1(){
  int wge, jw, xb, bh, n7d, cu, pj;

  wge=1+12;
  jw=0;
  xb=1;
  bh=4;
  n7d=16;
  cu=wge;
  pj=jw;

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
