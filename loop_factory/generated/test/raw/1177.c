int main1(){
  int xf, u, iq, q8, hi, p0, b;

  xf=(1%7)+6;
  u=xf;
  iq=(1%60)+60;
  q8=(1%9)+2;
  hi=0;
  p0=0;
  b=u;

  while (1) {
      if (iq<=q8*hi+p0) {
          break;
      }
      if (p0==q8-1) {
          p0 = 0;
          hi += 1;
      }
      else {
          p0++;
      }
      b = (hi-p0)+(b);
  }

}
