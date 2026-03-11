int main1(){
  int e6j, ci, r52, r06, a3;
  e6j=1*5;
  ci=0;
  r52=0;
  r06=0;
  a3=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a3 == ci;
  loop invariant r52 == ci / 9;
  loop invariant 0 <= ci <= e6j;
  loop invariant ci == 9*r52 + r06;
  loop invariant e6j == 5;
  loop assigns a3, ci, r06, r52;
*/
while (1) {
      if (!(ci<=e6j-1)) {
          break;
      }
      r06 = r06 + 1;
      a3++;
      if (r06>=9) {
          r06 = r06 - 9;
          r52++;
      }
      ci = ci + 1;
  }
}