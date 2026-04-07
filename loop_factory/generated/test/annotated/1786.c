int main1(int k){
  int ww, shl, le, k7x, z3, ywc;
  ww=10;
  shl=0;
  le=0;
  k7x=0;
  z3=0;
  ywc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ww + shl == 10;
  loop invariant (k7x > 0) ==> (le == 10 - ww);
  loop invariant 0 <= ww <= 10;
  loop invariant z3 == (10 - ww) * ywc;
  loop assigns ww, le, z3, shl;
*/
while (ww > 0) {
      ww -= 1;
      le = ((k7x > 0))+(le);
      z3 = z3 + ywc;
      shl = shl + 1;
  }
}