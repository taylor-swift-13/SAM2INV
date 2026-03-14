int main1(){
  int c, hcwe, np2f, nk67, xs, d;

  c=(1%29)+7;
  hcwe=1;
  np2f=0;
  nk67=0;
  xs=hcwe;
  d=c;

  while (1) {
      if (!(nk67<c)) {
          break;
      }
      np2f += 1;
      nk67 += 1;
      xs = xs*3+1;
      d += np2f;
  }

  while (1) {
      xs += nk67;
      nk67 = nk67*2;
      np2f = np2f + xs;
      hcwe = hcwe + 1;
      if (hcwe>=c) {
          break;
      }
  }

}
