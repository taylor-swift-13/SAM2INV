int main1(int q,int j){
  int z8, mw, ua, p;

  z8=89;
  mw=0;
  ua=1;
  p=0;

  while (p<z8) {
      ua = ua + q;
      p++;
      q += mw;
  }

  while (1) {
      if (!(p>0)) {
          break;
      }
      mw = mw + 1;
      q = q - 1;
      p -= 1;
  }

}
