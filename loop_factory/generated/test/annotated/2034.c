int main1(int q){
  int yybl, a8zh, tc6, tm;
  yybl=q;
  a8zh=1;
  tc6=1;
  tm=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tc6 == a8zh;
  loop invariant a8zh >= 1;
  loop invariant yybl == q - ((a8zh - 1) / 2) * ((a8zh - 1) / 2);
  loop invariant 2 * tm + 16 == 3 * (a8zh - 1);
  loop invariant (a8zh % 2) == 1;
  loop invariant yybl == \at(q, Pre) - (((a8zh - 1) / 2) * ((a8zh - 1) / 2));
  loop assigns yybl, tc6, tm, a8zh;
*/
while (1) {
      if (!(yybl >= a8zh)) {
          break;
      }
      yybl = yybl - a8zh;
      tc6 = (2)+(tc6);
      tm = tm + 3;
      a8zh += 2;
  }
}