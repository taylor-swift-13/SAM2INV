int main1(int m,int i){
  int ucr, so6, xo;

  ucr=i-10;
  so6=ucr;
  xo=0;

  while (1) {
      if (!(so6-1>=0)) {
          break;
      }
      xo = xo + 1;
      m = m*4+(xo%2)+3;
      so6++;
  }

}
