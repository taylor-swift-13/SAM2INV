int main1(int m,int n){
  int q, k, v, e, p, j;

  q=(n%9)+11;
  k=q;
  v=n;
  e=6;
  p=k;
  j=q;

  while (1) {
      if (k>=q) {
          break;
      }
      v = v+3;
      k = k+1;
      v = v+e;
  }

}
