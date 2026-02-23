int main1(int m,int p){
  int n, j, k, r;

  n=p;
  j=n;
  k=-6;
  r=j;

  while (j>0) {
      if (k+1<=n) {
          k = k+1;
      }
      else {
          k = n;
      }
      r = r+r;
      r = r+k;
  }

}
