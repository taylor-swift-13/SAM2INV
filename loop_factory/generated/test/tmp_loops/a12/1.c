int main1(int n){
  int s6, mf, wn;

  s6=n;
  mf=0;
  wn=4;

  for (; mf<s6; mf++) {
      wn = mf%5;
      if (mf>=wn) {
          wn = (mf-wn)%5;
          wn = wn+wn-wn;
      }
      else {
          wn = wn + wn;
      }
      n = n + wn;
  }

}
