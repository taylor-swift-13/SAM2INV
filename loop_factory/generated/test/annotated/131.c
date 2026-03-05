int main1(){
  int br, lj, chg, tj6;
  br=1+24;
  lj=3;
  chg=0;
  tj6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant br == 25;
  loop invariant br - lj >= 0;
  loop invariant tj6 == 0 && (chg == 0 || chg == 1);
  loop invariant 3 <= lj;
  loop assigns chg, tj6, lj;
*/
for (; chg>0&&lj<br; lj++) {
      if (chg<chg) {
          chg = chg;
      }
      else {
          chg = chg;
      }
      chg -= chg;
      tj6 += chg;
      chg = chg + 1;
  }
}