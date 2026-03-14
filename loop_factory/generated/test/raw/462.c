int main1(){
  int ft9, jmr, zx, a, yz;

  ft9=1;
  jmr=0;
  zx=0;
  a=-4;
  yz=0;

  while (zx<=ft9-1) {
      a = zx;
      yz = yz + a;
      zx += 1;
  }

  while (1) {
      if (!(jmr<zx)) {
          break;
      }
      yz = yz + 1;
      jmr += 1;
      a = a + yz;
  }

}
