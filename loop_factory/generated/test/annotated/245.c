int main1(){
  int fn, gy9, xxj;
  fn=1;
  gy9=3;
  xxj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xxj >= 0;
  loop invariant fn == 1;
  loop invariant gy9 == 3;
  loop invariant xxj <= fn + gy9;
  loop invariant xxj % 2 == 0;
  loop assigns xxj;
*/
while (xxj<fn) {
      if (xxj<fn/2) {
          xxj += 2;
      }
      else {
          xxj -= 2;
      }
      xxj++;
      xxj = xxj + gy9;
  }
}