int main1(){
  int e8, sj, t4, k0q, r, ml, ycr, fz, u5z;

  e8=(1%13)+7;
  sj=0;
  t4=9;
  k0q=0;
  r=sj;
  ml=-3;
  ycr=sj;
  fz=e8;
  u5z=0;

  while (sj<=e8-1) {
      if (!(!(sj%2==0))) {
          if (t4>0) {
              t4--;
              k0q++;
          }
      }
      else {
          if (k0q>0) {
              k0q -= 1;
              t4 = t4 + 1;
          }
      }
      sj += 1;
      r += t4;
      u5z += k0q;
      r = r + 1;
      fz = fz+(sj%2);
      ycr = ycr + sj;
      ml += r;
  }

}
