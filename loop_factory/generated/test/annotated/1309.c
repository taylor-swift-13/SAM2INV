int main1(){
  int sw2, e6n, f6;
  sw2=0;
  e6n=(1%28)+10;
  f6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f6 >= 0;
  loop invariant e6n == 11 - sw2*(sw2 - 1)/2;
  loop invariant sw2 >= 0;
  loop invariant 0 <= sw2 <= 5;
  loop assigns e6n, f6, sw2;
*/
while (e6n>sw2) {
      e6n -= sw2;
      f6 = f6 + e6n;
      sw2 += 1;
      f6 = f6*2;
  }
}