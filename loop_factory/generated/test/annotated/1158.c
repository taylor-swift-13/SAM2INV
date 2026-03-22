int main1(){
  int r, te, r0, g3, va;
  r=(1%28)+9;
  te=0;
  r0=0;
  g3=(1%28)+10;
  va=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 10;
  loop invariant te == 0;
  loop invariant g3 == 11 - r0*(r0 - 1)/2;
  loop invariant r0 >= 0;
  loop invariant va == -4 + r0 * (r + te);
  loop assigns g3, r0, va;
*/
while (g3>r0) {
      g3 -= r0;
      va += r;
      r0 = r0 + 1;
      va = va + te;
  }
}