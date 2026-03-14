int main1(){
  int e, l4p, xo, yn0, w2;

  e=66;
  l4p=2;
  xo=0;
  yn0=-8;
  w2=-1;

  while (xo<e) {
      if (w2<e) {
          yn0 = xo;
      }
      xo = xo + 1;
      w2 += l4p;
  }

  while (1) {
      xo = xo + yn0;
      yn0 = yn0 + w2;
      e += 1;
      if (e>=w2) {
          break;
      }
  }

}
