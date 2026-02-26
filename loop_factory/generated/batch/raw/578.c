int main1(int p,int q){
  int k, s, n, v;

  k=q+5;
  s=1;
  n=s;
  v=5;

  while (1) {
      if (s>=k) {
          break;
      }
      n = n+2;
      s = s+1;
      n = n*2;
      v = v+n;
  }

}
