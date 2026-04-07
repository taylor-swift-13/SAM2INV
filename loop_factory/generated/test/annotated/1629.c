int main1(){
  int s4, va9l, etn;
  s4=0;
  va9l=52;
  etn=26;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s4 + 3*etn == 78;
  loop invariant va9l == 3*etn - 26;
  loop invariant 0 <= etn;
  loop invariant etn <= 26;
  loop assigns s4, va9l, etn;
*/
while (etn>0) {
      s4 = s4 + 3;
      va9l = va9l - 3;
      etn--;
  }
}