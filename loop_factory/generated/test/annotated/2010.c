int main1(int f){
  int izlp, xk1, g0;
  izlp=f;
  xk1=53;
  g0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant izlp == \at(f, Pre);
  loop invariant f == (\at(f, Pre) + g0 * izlp);
  loop invariant xk1 + g0 == 53;
  loop invariant (0 <= g0 && g0 <= 53);
  loop invariant (0 <= xk1 && xk1 <= 53);
  loop assigns f, xk1, g0;
*/
while (1) {
      if (!(xk1>=1)) {
          break;
      }
      xk1--;
      f = f + izlp;
      g0++;
  }
}