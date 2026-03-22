int main1(){
  int sw2, e6n, f6;

  sw2=0;
  e6n=(1%28)+10;
  f6=0;

  while (e6n>sw2) {
      e6n -= sw2;
      f6 = f6 + e6n;
      sw2 += 1;
      f6 = f6*2;
  }

}
