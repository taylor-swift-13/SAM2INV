int main1(){
  int mbo, c0, dqt, dw, mw;

  mbo=1;
  c0=(1%40)+2;
  dqt=0;
  dw=-5;
  mw=mbo;

  while (c0!=dqt) {
      dqt = c0;
      c0 = (c0+mbo/c0)/2;
      dw = dw + 3;
      mw = (mw+c0)+(-(dqt));
      dw = dw*dw+dw;
  }

}
