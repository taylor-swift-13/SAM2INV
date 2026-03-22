int main1(int c){
  int nfh, kn, e, ltu;

  nfh=c+24;
  kn=0;
  e=1;
  ltu=1;

  while (1) {
      if (!(e<=nfh)) {
          break;
      }
      ltu += 2;
      kn++;
      c = c + ltu;
      e = e + ltu;
  }

}
