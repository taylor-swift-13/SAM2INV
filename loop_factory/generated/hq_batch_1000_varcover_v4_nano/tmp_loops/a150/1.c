int main1(int b,int m,int n,int q){
  int l, i, v, u, t, r, a, h;

  l=b+18;
  i=0;
  v=i;
  u=q;
  t=n;
  r=b;
  a=m;
  h=n;

  while (i<l) {
      r = v+u+t;
      v = v+1;
      h = h+r;
      u = u+1;
      r = r+i;
      a = a+1;
      r = r+(-2);
      i = i+3;
  }

}
