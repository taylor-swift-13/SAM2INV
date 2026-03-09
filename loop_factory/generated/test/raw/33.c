int main1(int n){
  int p, hc, v5z9, t31;

  p=n;
  hc=2;
  v5z9=0;
  t31=n;

  while (1) {
      v5z9 += 4;
      t31 -= 4;
      n += v5z9;
      n = v5z9-8;
      hc += 1;
      if (hc>=p) {
          break;
      }
  }

}
