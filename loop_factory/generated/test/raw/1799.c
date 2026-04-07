int main1(){
  int c, sldn, dtb4, z, k;

  c=1;
  sldn=c+5;
  dtb4=sldn;
  z=sldn;
  k=sldn;

  while (1) {
      if (!(sldn>=1)) {
          break;
      }
      dtb4 = dtb4*4;
      z = z/4;
      k = k*4+(dtb4%5)+2;
      sldn = 0;
  }

}
