int main1(int a,int b,int k,int q){
  int l, i, v, h, n, r, e;

  l=b;
  i=l;
  v=2;
  h=k;
  n=k;
  r=-5;
  e=k;

  while (i>0) {
      if (v+1<=l) {
          v = v+1;
      }
      else {
          v = l;
      }
      v = v+h;
      h = h+n;
      n = n+3;
      v = v+h;
      v = v*v+n;
      n = n*n+e;
  }

}
