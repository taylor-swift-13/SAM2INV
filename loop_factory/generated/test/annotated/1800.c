int main1(){
  int b6, h7, qg, ojd1, k9r, gs;
  b6=1;
  h7=0;
  qg=20;
  ojd1=3;
  k9r=1+4;
  gs=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ojd1 == 3 + 3 * h7;
  loop invariant 0 <= h7;
  loop invariant h7 <= b6;
  loop invariant k9r >= 5;
  loop invariant qg >= 20;
  loop invariant b6 == 1;
  loop assigns qg, h7, k9r, ojd1;
*/
while (h7 < b6) {
      qg = qg * ojd1 + gs;
      h7 = h7 + 1;
      k9r += qg;
      ojd1 = ojd1 + 3;
  }
}