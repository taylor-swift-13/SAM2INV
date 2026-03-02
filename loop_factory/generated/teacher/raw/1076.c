int main1(int a,int n){
  int v, r, b, m;

  v=n+3;
  r=3;
  b=r;
  m=n;

  while (r<v) {
      b = b+m;
      m = m+m;
      r = r+1;
  }

}
