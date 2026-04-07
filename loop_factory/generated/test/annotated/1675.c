int main1(){
  int il5, pw, am, m, my;
  il5=(1%32)+14;
  pw=0;
  am=0;
  m=pw;
  my=il5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant my == il5 * (am/2 + 1);
  loop invariant 0 <= am;
  loop invariant am % 2 == 0;
  loop invariant am <= il5 + 1;
  loop invariant ((am == 0 && m == 0) || (am > 0 && m == am + 1));
  loop assigns am, m, my;
*/
while (am+2<=il5+2-1) {
      m = am+3;
      my += il5;
      am += 2;
  }
}