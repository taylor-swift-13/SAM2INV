int main1(){
  int o8, ka9, omb, p0n, bd70, g5;

  o8=35;
  ka9=0;
  omb=0;
  p0n=(1%28)+10;
  bd70=o8;
  g5=8;

  while (p0n>omb) {
      p0n -= omb;
      g5 = g5 + ka9;
      bd70++;
      omb = omb + 1;
  }

  while (ka9>g5) {
      ka9 -= g5;
      g5 = g5 + 1;
      g5 = g5*4+1;
      ka9 = ka9*g5+1;
  }

}
