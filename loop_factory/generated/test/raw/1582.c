int main1(){
  int uxl, gk, nn, ho, im, j, u, z, v6h, i1p, b0k;

  uxl=40;
  gk=uxl;
  nn=1;
  ho=0;
  im=gk;
  j=0;
  u=uxl;
  z=0;
  v6h=0;
  i1p=uxl;
  b0k=0;

  while (gk-1>=0) {
      nn++;
      ho = ho - 1;
      if (j<v6h+1) {
          u = i1p-u;
      }
      if (u<i1p+1) {
          v6h += gk;
      }
      im += gk;
      z = im+j+u;
      b0k += gk;
      im++;
      i1p = (1)+(i1p);
      u += gk;
      gk = gk + 1;
  }

}
