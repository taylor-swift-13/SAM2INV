int main1(int a){
  int rhx, xf, bv, sw, pp;
  rhx=(a%20)+15;
  xf=0;
  bv=24;
  sw=1;
  pp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sw == pp + 1;
  loop invariant xf == pp;
  loop invariant (pp*(pp+1) <= 48) ==> (bv == 24 - (pp*(pp+1))/2);
  loop invariant rhx == (\at(a, Pre) % 20) + 15;
  loop invariant 0 <= bv;
  loop invariant bv <= 24;
  loop invariant sw >= 1;
  loop assigns bv, pp, sw, xf;
*/
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