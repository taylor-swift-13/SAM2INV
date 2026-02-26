int main1(int b,int q){
  int n, t, k, u;

  n=q;
  t=0;
  k=-2;
  u=n;

  while (t<=n-3) {
      if (t<n/2) {
          k = k+u;
      }
      else {
          k = k+1;
      }
      k = k+5;
  }

}
