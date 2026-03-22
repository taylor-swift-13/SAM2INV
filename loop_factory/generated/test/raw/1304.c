int main1(int q,int o){
  int bcmr, kdf, oq, n;

  bcmr=1;
  kdf=o;
  oq=o;
  n=(o%35)+8;

  while (1) {
      if (!(n>0)) {
          break;
      }
      bcmr = bcmr+kdf*kdf;
      oq = oq+n*n;
      kdf = kdf+n*n;
      q = q + kdf;
      n = n - 1;
  }

}
