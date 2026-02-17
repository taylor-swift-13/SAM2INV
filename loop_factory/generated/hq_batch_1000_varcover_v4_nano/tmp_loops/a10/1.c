int main1(int a,int n,int p,int q){
  int l, i, v, e, x, w, u, t, h;

  l=p-3;
  i=0;
  v=5;
  e=a;
  x=4;
  w=a;
  u=p;
  t=q;
  h=p;

  while (i<l) {
      v = v+1;
      e = e+1;
      w = w*w+v;
      v = v%7;
      e = e*x;
      e = e%9;
      t = t*2;
  }

}
