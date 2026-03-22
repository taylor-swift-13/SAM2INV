int main1(){
  int a0, x, okb, lm7, jug, f;

  a0=2;
  x=0;
  okb=0;
  lm7=(1%50)+20;
  jug=(1%8)+2;
  f=-1;

  while (1) {
      if (!(lm7!=0)) {
          break;
      }
      if (okb+1==jug) {
          x = x + 1;
          okb = 0;
      }
      else {
          okb++;
      }
      lm7 = lm7 - 1;
      jug = jug + a0;
      f = f/4;
      jug = jug*4;
  }

}
