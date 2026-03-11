int main1(){
  int sz, fx, ga, xfg, jtn5, g;

  sz=1+18;
  fx=0;
  ga=0;
  xfg=0;
  jtn5=0;
  g=6;

  while (fx<sz) {
      xfg = fx%5;
      if (!(!(fx>=g))) {
          jtn5 = (fx-g)%5;
          ga = ga+xfg-jtn5;
      }
      else {
          ga = ga + xfg;
      }
      fx = fx + 1;
      g = g + xfg;
  }

}
