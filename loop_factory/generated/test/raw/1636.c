int main1(int x){
  int k4ko, kzow, egq;

  k4ko=x+8;
  kzow=-3;
  egq=k4ko;

  while (1) {
      if (!(kzow<=k4ko-1)) {
          break;
      }
      egq = k4ko-kzow;
      kzow = kzow + 1;
      x = x + k4ko;
  }

}
