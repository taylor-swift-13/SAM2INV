int main1(int b,int k,int p,int q){
  int l, i, v, x, n, m, e, a, f, o;

  l=k+5;
  i=l;
  v=p;
  x=i;
  n=i;
  m=q;
  e=4;
  a=q;
  f=k;
  o=b;

  while (i>0) {
      m = m*m+v;
      v = v%9;
      if (i+5<=v+l) {
          x = x*x+a;
      }
      else {
          v = v*2;
      }
      i = i-1;
  }

}
