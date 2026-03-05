int main1(int l){
  int k, kc, ly;

  k=75;
  kc=0;
  ly=0;

  while (kc<k) {
      if (kc%2==0) {
          if (ly>0) {
              ly -= 1;
              ly++;
          }
      }
      else {
          if (ly>0) {
              ly -= 1;
              ly++;
          }
      }
      kc += 1;
      l = l + ly;
  }

}
