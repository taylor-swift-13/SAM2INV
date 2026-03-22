int main1(){
  int l9x, dp, li, yf;

  l9x=1+12;
  dp=0;
  li=(1%28)+10;
  yf=l9x;

  while (1) {
      if (!(li>dp)) {
          break;
      }
      li -= dp;
      dp += 1;
      yf = ((li%3))+(yf);
  }

}
