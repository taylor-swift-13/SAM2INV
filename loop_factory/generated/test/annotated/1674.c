int main1(){
  int a, oe, but, ms;
  a=1+25;
  oe=0;
  but=-6;
  ms=oe;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == 26;
  loop invariant ms == (oe + 1) / 2;
  loop invariant but == -6 + 4 * oe;
  loop invariant 0 <= oe;
  loop invariant oe <= a;
  loop assigns oe, ms, but;
*/
while (oe < a) {
      oe += 1;
      ms = ms+(oe%2);
      but += 4;
  }
}