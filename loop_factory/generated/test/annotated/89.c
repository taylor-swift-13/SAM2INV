int main1(){
  int iza, s0qi, zvry, x;
  iza=1;
  s0qi=0;
  zvry=0;
  x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zvry == x % 4;
  loop invariant iza == 1;
  loop invariant s0qi == 0;
  loop invariant 0 <= x <= iza;
  loop assigns zvry, x;
*/
while (x<iza) {
      zvry = (zvry+1)%4;
      x = x + 1;
      if (s0qi+5<=s0qi+iza) {
          zvry = zvry + zvry;
      }
  }
}