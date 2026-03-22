int main1(){
  int jph, ef, lv9, ktb7, orw2;
  jph=1+12;
  ef=1;
  lv9=ef;
  ktb7=0;
  orw2=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ef == 1) ==> (lv9 == 1 && ktb7 == 0);
  loop invariant (ef >= 2) ==> (ktb7 == orw2*orw2) && (lv9 % 3 == 0);
  loop invariant 1 <= ef;
  loop invariant ef <= jph;
  loop invariant lv9 >= 1;
  loop invariant (ktb7 == 0) || (ktb7 == orw2 * orw2);
  loop invariant jph == 13;
  loop invariant orw2 == 6;
  loop assigns lv9, ktb7, ef;
*/
while (1) {
      if (!(ef<=jph-1)) {
          break;
      }
      lv9 = lv9*3;
      ktb7 = ktb7/3;
      ktb7 = orw2*orw2;
      ef += 1;
  }
}