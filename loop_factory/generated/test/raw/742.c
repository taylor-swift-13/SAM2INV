int main1(){
  int so, d8, b2, okm;

  so=40;
  d8=0;
  b2=(1%28)+10;
  okm=so;

  while (b2>d8) {
      b2 -= d8;
      d8 = d8 + 1;
      okm += b2;
  }

}
