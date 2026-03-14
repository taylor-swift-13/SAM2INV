int main1(){
  int mnr, zsh, n4c, zw, ltp;

  mnr=1*4;
  zsh=mnr;
  n4c=0;
  zw=0;
  ltp=mnr;

  while (1) {
      if (!(n4c<=mnr-1)) {
          break;
      }
      zw = zw + n4c;
      n4c = n4c + 1;
      ltp = ltp + zsh;
  }

  while (1) {
      zsh = zsh + zsh;
      mnr = mnr + 1;
      if (mnr>=ltp) {
          break;
      }
  }

}
