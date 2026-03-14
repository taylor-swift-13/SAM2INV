int main1(int x){
  int d4, hfy, atr, kln4, ajtl;

  d4=61;
  hfy=0;
  atr=0;
  kln4=0;
  ajtl=(x%18)+5;

  while (ajtl>=1) {
      kln4 = kln4+x*x;
      atr = atr+x*x;
      ajtl -= 1;
      hfy = hfy+x*x;
      x += d4;
  }

  while (1) {
      hfy = hfy + 1;
      if (hfy>=atr) {
          break;
      }
  }

}
