int main1(){
  int mv, p9xx, ef7;
  mv=1;
  p9xx=0;
  ef7=1*2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mv == 1;
  loop invariant p9xx >= 0;
  loop invariant p9xx <= mv;
  loop invariant ef7 == 2 * (p9xx + 1);
  loop assigns ef7, p9xx;
*/
while (1) {
      ef7 = ef7*2;
      p9xx++;
      if (p9xx>=mv) {
          break;
      }
  }
}