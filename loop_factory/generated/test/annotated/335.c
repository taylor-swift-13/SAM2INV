int main1(){
  int to, tk, g, fx, ik;
  to=1*3;
  tk=to;
  g=0;
  fx=0;
  ik=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == fx;
  loop invariant ik == fx * (fx + 1) / 2;
  loop invariant 0 <= fx;
  loop invariant to >= fx;
  loop assigns g, fx, ik;
*/
while (1) {
      if (!(fx<to)) {
          break;
      }
      g++;
      fx = fx + 1;
      ik += fx;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tk <= to;
  loop invariant fx - 2*tk == -3;
  loop invariant fx >= 0;
  loop invariant fx <= to;
  loop assigns fx, tk;
*/
while (tk<to) {
      tk++;
      fx = fx + 1;
      fx = fx + 1;
  }
}