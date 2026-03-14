int main1(){
  int tr, lm7, x;
  tr=1+9;
  lm7=1;
  x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tr == 10;
  loop invariant x % 6 == 0;
  loop invariant x >= 0;
  loop invariant x/6 <= lm7 - 1;
  loop assigns x, lm7;
*/
while (1) {
      if (!(lm7<=tr)) {
          break;
      }
      x = x + 1;
      lm7 = 2*lm7;
      x = x + 5;
  }
}