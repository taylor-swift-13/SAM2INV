int main1(){
  int jmx, h, w2, kw;

  jmx=10;
  h=0;
  w2=h;
  kw=0;

  while (1) {
      if (!(h < jmx)) {
          break;
      }
      w2 = w2 + (1 - 2*(2*h/jmx));
      h += 1;
      kw = kw + w2;
  }

}
