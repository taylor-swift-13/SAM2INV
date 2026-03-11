int main1(){
  int lwb, qn, az, qm, d;

  lwb=73;
  qn=lwb;
  az=0;
  qm=0;
  d=0;

  while (1) {
      if (!(qn<lwb)) {
          break;
      }
      d++;
      qm = qm + 1;
      if (qm>=11) {
          qm -= 11;
          az = az + 1;
      }
      qn++;
  }

}
