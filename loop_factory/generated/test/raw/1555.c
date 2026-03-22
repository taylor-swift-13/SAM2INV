int main1(){
  int d, n, i, zb, kzj6, d0, d9v, zdcm, f9;

  d=1*2;
  n=0;
  i=0;
  zb=0;
  kzj6=0;
  d0=0;
  d9v=0;
  zdcm=1;
  f9=0;

  while (n < d) {
      if (n % 3 == 0) {
          i = i + 1;
          d0 = d0 + i;
      }
      if (n % 3 == 1) {
          zb++;
          kzj6 += 1;
      }
      if (n % 3 == 2) {
          f9 += zdcm;
          zdcm++;
      }
      n += 1;
      d9v += n;
      if (!(!(d9v+6<d))) {
          d9v = d9v + d9v;
      }
      else {
          d9v = d9v - d9v;
      }
      d9v = d9v + d9v;
      d9v += n;
  }

}
