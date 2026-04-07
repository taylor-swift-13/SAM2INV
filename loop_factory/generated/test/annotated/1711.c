int main1(){
  int jyy, ym, om, p, dte;
  jyy=1;
  ym=0;
  om=0;
  p=0;
  dte=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (p == ym);
  loop invariant (ym <= jyy);
  loop invariant om == p;
  loop invariant dte == ym;
  loop invariant (0 <= ym);
  loop assigns ym, p, om, dte;
*/
while (ym < jyy) {
      ym += 1;
      p = ym;
      om = p;
      dte = om;
  }
}