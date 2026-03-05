int main1(){
  int pp3, yqr, jj, o908;
  pp3=(1%10)+20;
  yqr=0;
  jj=0;
  o908=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pp3 == (1 % 10) + 20;
  loop invariant 0 <= o908 <= 1;
  loop invariant yqr >= 0;
  loop invariant yqr <= pp3;
  loop invariant jj >= yqr;
  loop invariant jj <= 2*yqr;
  loop assigns jj, o908, yqr;
*/
while (yqr<pp3) {
      jj += 1;
      o908 += 1;
      if (o908>=2) {
          o908 -= 2;
          jj += 1;
      }
      yqr = yqr + 1;
  }
}