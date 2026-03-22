int main1(int m,int q){
  int igv, cbd, z1qh, se4g, nyi, dtb, u, gb;

  igv=m-8;
  cbd=0;
  z1qh=4;
  se4g=4;
  nyi=0;
  dtb=4;
  u=0;
  gb=cbd;

  while (1) {
      if (!(cbd<igv)) {
          break;
      }
      if (!(!(cbd%3==0))) {
          if (z1qh>0) {
              z1qh -= 1;
              nyi = nyi + 1;
          }
      }
      else {
          if (z1qh<dtb) {
              z1qh++;
              se4g += 1;
          }
      }
      cbd = cbd + 1;
      u = u + 1;
      dtb = dtb + se4g;
      dtb += 1;
      gb += dtb;
      m = m + gb;
  }

}
