int main1(){
  int ltod, ifwn, fl, r0p, nf2q, zwad, kpa, qf;

  ltod=1;
  ifwn=ltod+3;
  fl=1;
  r0p=1;
  nf2q=1;
  zwad=1;
  kpa=2;
  qf=1;

  while (1) {
      if (!(nf2q<=ltod)) {
          break;
      }
      fl = fl*(1/nf2q);
      if ((nf2q/2)%2==0) {
          zwad = 1;
      }
      else {
          zwad = -1;
      }
      nf2q = nf2q + 1;
      r0p = r0p+zwad*fl;
      fl = fl*(1/nf2q);
      if (qf+6<ltod) {
          qf = kpa*kpa;
      }
      kpa += zwad;
      kpa += ifwn;
  }

}
