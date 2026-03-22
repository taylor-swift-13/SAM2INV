int main1(){
  int pv, r4, m, r8ia, i62;
  pv=36;
  r4=0;
  m=1;
  r8ia=6;
  i62=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r8ia == 6 + 2*i62;
  loop invariant r4 % 3 == 0;
  loop invariant m == i62 + 1;
  loop invariant 0 <= i62 <= pv + 1;
  loop assigns r4, i62, m, r8ia;
*/
while (1) {
      if (!(i62<=pv)) {
          break;
      }
      r4 = r4 + m;
      i62 += 1;
      m += r8ia;
      r8ia += 2;
      r4 = r4*3;
      m = m/3;
  }
}