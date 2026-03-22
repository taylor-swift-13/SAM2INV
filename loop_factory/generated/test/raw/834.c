int main1(){
  int r3, lo, p, mfi, m, hv;

  r3=77;
  lo=0;
  p=lo;
  mfi=lo;
  m=0;
  hv=(1%6)+2;

  while (1) {
      if (m>=r3) {
          break;
      }
      m++;
      p = p*hv+1;
      mfi = mfi*hv;
      hv = hv+(mfi%9);
  }

}
