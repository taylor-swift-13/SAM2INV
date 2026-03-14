int main1(){
  int c, gk8, k, p2;
  c=1+11;
  gk8=0;
  k=-5;
  p2=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= gk8;
  loop invariant gk8 <= c;
  loop invariant p2 == -5 + gk8 * c;
  loop assigns k, p2, gk8;
*/
while (1) {
      if (!(gk8<c)) {
          break;
      }
      k = c-gk8;
      p2 = p2 + c;
      gk8 += 1;
  }
}