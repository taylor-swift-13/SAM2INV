int main1(){
  int oqcm, m, cu, mj, zr0, ie;

  oqcm=(1%8)+5;
  m=oqcm;
  cu=90;
  mj=0;
  zr0=1;
  ie=0;

  while (cu>0&&m<oqcm) {
      if (cu<=zr0) {
          ie = cu;
      }
      else {
          ie = zr0;
      }
      mj += ie;
      cu -= ie;
      m++;
      zr0 += 1;
  }

}
