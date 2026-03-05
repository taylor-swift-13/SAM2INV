int main1(int t){
  int rgj, rxd;

  rgj=(t%10)+11;
  rxd=0;

  while (rxd<rgj) {
      rxd = (rxd+1)%3;
      rxd++;
      t += rxd;
  }

}
