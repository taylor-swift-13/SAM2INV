int main1(int m,int p){
  int n, l, x;

  n=22;
  l=0;
  x=n;

  while (l<=n-3) {
      x = x+2;
      if (x+4<n) {
          x = x+x;
      }
  }

}
