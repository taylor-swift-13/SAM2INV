int main1(){
  int pzz3, qlf, hz5w;
  pzz3=(1%33)+8;
  qlf=0;
  hz5w=pzz3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hz5w == pzz3 + qlf*(qlf - 1)/2;
  loop invariant 0 <= qlf <= pzz3;
  loop assigns hz5w, qlf;
*/
while (1) {
      hz5w = hz5w + qlf;
      qlf += 1;
      if (qlf>=pzz3) {
          break;
      }
  }
}