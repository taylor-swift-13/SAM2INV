int main179(int a,int p,int q){
  int n, t, v, l;

  n=p+7;
  t=n+5;
  v=t;
  l=p;

  while (1) {
      if (t>=n) {
          break;
      }
      v = v+1;
      t = t+1;
      v = v*2;
  }

  while (t<n) {
      l = l+4;
  }

  while (1) {
      if (v+2<=n) {
          v = v+2;
      }
      else {
          v = n;
      }
      v = v+t;
  }

}
