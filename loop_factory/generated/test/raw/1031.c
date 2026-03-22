int main1(){
  int p, e, gj, hqw, zff;

  p=1;
  e=p;
  gj=0;
  hqw=0;
  zff=e;

  while (1) {
      if (!(e-1>=0)) {
          break;
      }
      gj += 1;
      hqw = hqw + gj;
      e += 1;
  }

  while (1) {
      if (!(p-1>=0)) {
          break;
      }
      zff += p;
      zff += zff;
      p -= 1;
  }

}
