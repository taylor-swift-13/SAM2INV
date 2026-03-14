int main1(int a){
  int rhx, xf, bv, sw, pp;

  rhx=(a%20)+15;
  xf=0;
  bv=24;
  sw=1;
  pp=0;

  while (bv>0&&sw<=rhx) {
      if (bv>sw) {
          bv -= sw;
      }
      else {
          bv = 0;
      }
      pp += 1;
      xf = xf + 1;
      sw = sw + 1;
  }

}
