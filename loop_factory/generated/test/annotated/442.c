int main1(){
  int pm, ca, oa, gaku, nu1t;
  pm=1+16;
  ca=3;
  oa=0;
  gaku=0;
  nu1t=pm;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= oa;
  loop invariant oa <= pm;
  loop invariant gaku == (oa*(oa-1))/2;
  loop invariant nu1t == pm + ca*oa;
  loop assigns gaku, oa, nu1t;
*/
while (oa<pm) {
      gaku += oa;
      oa++;
      nu1t += ca;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nu1t <= gaku;
  loop assigns nu1t;
*/
while (1) {
      if (!(nu1t<gaku)) {
          break;
      }
      nu1t += 1;
  }
}