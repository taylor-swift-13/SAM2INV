int main1(){
  int qny, e7, ewd, chcj;
  qny=1;
  e7=0;
  ewd=2;
  chcj=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ewd == e7 + 2;
  loop invariant qny == 1;
  loop invariant 0 <= e7 <= qny;
  loop assigns chcj, ewd, e7;
*/
while (e7<=qny-1) {
      if (ewd>=9) {
          chcj = -1;
      }
      if (ewd<=2) {
          chcj = 1;
      }
      ewd += chcj;
      e7 = e7 + 1;
  }
}