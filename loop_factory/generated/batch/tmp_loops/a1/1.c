int main1(int m,int n){
  int q, k, v, e, p, j;

  q=(n%9)+11;
  k=q;
  v=0;
  e=n;
  p=6;
  j=k;

  while (k-2>=0) {
      e = q-v;
      v = v+1;
      j = v+e+p;
      v = v+1;
      v = v+k;
  }

}
