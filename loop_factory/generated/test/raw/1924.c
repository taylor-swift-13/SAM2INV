int main1(){
  int om, pu, uhb, w, xo, m, c6j4;

  om=1;
  pu=0;
  uhb=16;
  w=0;
  xo=25;
  m=om;
  c6j4=om;

  while (pu<om) {
      if (!(!(pu%2==0))) {
          if (uhb>0) {
              uhb -= 1;
              w += 1;
          }
      }
      else {
          if (w>0) {
              w = w - 1;
              uhb++;
          }
      }
      pu++;
      c6j4 += 1;
      xo = xo+(pu%2);
      xo = xo + 1;
      m = m + xo;
  }

}
