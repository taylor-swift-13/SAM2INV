int main1(int t){
  int r44, b, mw, fyp, s;

  r44=(t%40)+5;
  b=r44;
  mw=1;
  fyp=0;
  s=-1;

  while (mw<=r44) {
      fyp = fyp+2*mw-1;
      s += b;
      mw = mw + 1;
      s++;
  }

}
