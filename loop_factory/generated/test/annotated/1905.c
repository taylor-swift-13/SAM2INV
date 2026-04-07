int main1(){
  int ccl, am, a, txe, cm, ub, ngq, ih;
  ccl=(1%20)+15;
  am=0;
  a=am;
  txe=am;
  cm=ccl;
  ub=am;
  ngq=1;
  ih=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == (am + 2) / 3;
  loop invariant cm == ccl + am / 3;
  loop invariant txe == (am + 1) / 3;
  loop invariant 0 <= am <= ccl;
  loop invariant ub >= 0;
  loop invariant cm == 16 + am / 3;
  loop assigns a, am, txe, cm, ub, ih, ngq;
*/
while (1) {
      if (!(am < ccl)) {
          break;
      }
      if ((am % 3) == 0) {
          a++;
      }
      if ((am % 3) == 1) {
          txe++;
      }
      if ((am % 3) == 2) {
          cm++;
      }
      else {
      }
      ub = ub + a;
      ih += cm;
      ngq += 2;
      am += 1;
      ngq = ngq + ih;
  }
}