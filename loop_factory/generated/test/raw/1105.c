int main1(){
  int c9, q1rg, x, b, kr, lc, l;

  c9=1*2;
  q1rg=0;
  x=1;
  b=0;
  kr=q1rg;
  lc=q1rg;
  l=4;

  while (x<=c9) {
      b = b+x*x;
      x = x + 1;
      kr += b;
      kr = kr+lc+l;
  }

  while (1) {
      lc = lc + 1;
      if (lc>=l) {
          break;
      }
  }

}
