int main1(int b,int n){
  int l, v, m, k;

  l=n;
  v=0;
  m=b;
  k=n;

  while (m!=0&&k!=0) {
      if (m>k) {
          m = m-k;
      }
      else {
          k = k-m;
      }
  }

}
