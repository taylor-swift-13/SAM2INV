int main1(){
  int o8, ka9, omb, p0n, bd70, g5;
  o8=35;
  ka9=0;
  omb=0;
  p0n=(1%28)+10;
  bd70=o8;
  g5=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p0n == 11 - (omb*(omb-1))/2;
  loop invariant bd70 == 35 + omb;
  loop invariant g5 == 8;
  loop invariant ka9 == 0;
  loop invariant o8 == 35;
  loop assigns p0n, g5, bd70, omb;
*/
while (p0n>omb) {
      p0n -= omb;
      g5 = g5 + ka9;
      bd70++;
      omb = omb + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g5 >= 8;
  loop invariant o8 == 35;
  loop invariant ka9 >= 0;
  loop assigns ka9, g5;
*/
while (ka9>g5) {
      ka9 -= g5;
      g5 = g5 + 1;
      g5 = g5*4+1;
      ka9 = ka9*g5+1;
  }
}