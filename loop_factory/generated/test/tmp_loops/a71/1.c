int main1(int p){
  int vdim, nk, qhm, gi, kqd, ru, n1, i2;

  vdim=71;
  nk=vdim;
  qhm=32;
  gi=0;
  kqd=1;
  ru=0;
  n1=1;
  i2=p+5;

  while (1) {
      if (!(qhm>0&&nk<vdim)) {
          break;
      }
      ru = kqd;
      if (qhm>=kqd) {
          qhm -= kqd;
          gi += kqd;
      }
      else {
          gi += qhm;
          qhm = 0;
      }
      nk++;
      kqd += 1;
      if (nk+6<=qhm+vdim) {
          i2 = i2+(-5);
      }
      n1 += kqd;
      n1 = n1 + 1;
      i2 = i2 + n1;
  }

}
