int main1(){
  int eq, wu, ka, wa, g, j;
  eq=1+13;
  wu=(1%28)+8;
  ka=(1%22)+5;
  wa=0;
  g=eq;
  j=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wu > 0;
  loop invariant (wu % 9) == 0;
  loop invariant wa >= 0;
  loop invariant g >= 0;
  loop invariant j >= 0;
  loop invariant wa % 9 == 0;
  loop invariant 0 <= ka <= 6;
  loop assigns wa, wu, ka, g, j;
*/
while (ka!=0) {
      if (ka%2==1) {
          wa += wu;
          ka--;
      }
      wu = 2*wu;
      ka = ka/2;
      g = g*3+(wu%4)+3;
      j = j*4+(wa%3)+3;
  }
}