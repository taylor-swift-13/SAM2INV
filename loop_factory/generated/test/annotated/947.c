int main1(int i){
  int q, kp, x;
  q=1;
  kp=(i%20)+10;
  x=(i%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kp == ((i % 20) + 10) - ((q - 1) / 2);
  loop invariant x  == ((i % 15) + 8)  - (q / 2);
  loop invariant (kp + x) + (q - 1) == ((\at(i, Pre) % 20) + 10) + ((\at(i, Pre) % 15) + 8);
  loop invariant (q >= 1);
  loop assigns kp, x, q;
*/
while (1) {
      if (!(kp>0&&x>0)) {
          break;
      }
      if (q%2==0) {
          kp--;
      }
      else {
          x--;
      }
      q += 1;
  }
}