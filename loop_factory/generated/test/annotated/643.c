int main1(int k){
  int iz5, g, co, cqwl, d;
  iz5=192;
  g=0;
  co=0;
  cqwl=k;
  d=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iz5 == 192;
  loop invariant g == 0;
  loop invariant d == 0;
  loop invariant 0 <= co <= iz5;
  loop invariant (co % 4) == 0;
  loop invariant ((co == 0) ==> (cqwl == k)) && ((co > 0) ==> (cqwl + co == iz5 + 4));
  loop assigns cqwl, co, d;
*/
while (1) {
      if (!(co<iz5)) {
          break;
      }
      cqwl = iz5-co;
      co += 4;
      d = d + g;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= iz5 <= 192;
  loop assigns iz5;
*/
for (; iz5-1>=0; iz5 -= 1) {
  }
}