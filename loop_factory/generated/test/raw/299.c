int main1(){
  int d1, rox, d0, kf;

  d1=(1%33)+12;
  rox=0;
  d0=0;
  kf=8;

  while (1) {
      if (!(rox<d1)) {
          break;
      }
      rox = rox + 1;
      d0 = (d1)+(-(rox));
      kf += d0;
  }

  while (1) {
      rox += d0;
      d0++;
      if (d0>=kf) {
          break;
      }
  }

}
