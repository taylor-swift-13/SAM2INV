int main1(int y){
  int l7k7, tv, vo, sbcr, xj5, i, jiq, ux, hh;

  l7k7=(y%37)+12;
  tv=0;
  vo=16;
  sbcr=0;
  xj5=0;
  i=tv;
  jiq=l7k7;
  ux=0;
  hh=y+2;

  while (tv<l7k7) {
      if (tv%2==0) {
          if (vo>0) {
              vo -= 1;
              sbcr = sbcr + 1;
          }
      }
      else {
          if (sbcr>0) {
              sbcr--;
              vo++;
          }
      }
      xj5 = xj5 + i;
      tv = tv + 1;
      jiq = jiq+(sbcr%7);
      hh = hh+(sbcr%8);
      i += jiq;
      jiq = jiq + 1;
      ux = xj5*xj5;
  }

}
