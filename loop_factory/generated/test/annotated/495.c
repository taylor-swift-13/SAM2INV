int main1(){
  int b92, tp, s8, em, s4;
  b92=68;
  tp=0;
  s8=(1%28)+10;
  em=5;
  s4=b92;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant em >= 5;
  loop invariant s8 >= 0;
  loop invariant tp >= 0;
  loop invariant s8 == 11 - tp*(tp-1)/2;
  loop invariant 68 <= s4 <= 68 + 7*tp;
  loop invariant b92 == 68;
  loop assigns s8, tp, s4, em;
*/
while (s8>tp) {
      s8 -= tp;
      tp = tp + 1;
      s4 = s4+(s8%8);
      em = em+(tp%7);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b92 >= tp;
  loop invariant b92 >= 68;
  loop assigns b92;
*/
while (1) {
      b92++;
      if (b92>=tp) {
          break;
      }
  }
}