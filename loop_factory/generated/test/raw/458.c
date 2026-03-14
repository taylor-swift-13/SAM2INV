int main1(int n,int k){
  int fny, i9f, v6, t, p9;

  fny=n;
  i9f=0;
  v6=3;
  t=0;
  p9=k;

  while (1) {
      if (!(t<fny)) {
          break;
      }
      v6 += n;
      t += 1;
      n = n+fny-i9f;
      p9 += t;
  }

  while (1) {
      if (!(p9<=fny-1)) {
          break;
      }
      i9f += 2;
      v6 += n;
      p9++;
      n += t;
  }

}
