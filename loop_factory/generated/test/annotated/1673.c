int main1(){
  int i8, mi, x, wa;
  i8=63;
  mi=0;
  x=-2;
  wa=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mi == wa;
  loop invariant ((mi == 0) ==> (x == -2)) && ((mi != 0) ==> (x == mi - 1)) && (0 <= mi) && (0 <= wa) && (mi <= i8) && (wa <= i8);
  loop assigns x, mi, wa;
*/
while (1) {
      if (!(mi<i8)) {
          break;
      }
      if (wa<i8) {
          x = mi;
      }
      wa = wa + 1;
      mi++;
  }
}