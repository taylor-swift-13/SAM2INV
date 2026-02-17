int main1(int a,int b,int k,int m){
  int l, i, v, r, e, y, p, c, t, q;

  l=(k%15)+17;
  i=0;
  v=8;
  r=m;
  e=a;
  y=l;
  p=m;
  c=a;
  t=m;
  q=k;

  while (i<l) {
      v = v+i;
      r = r*r;
      e = e+v*r;
      v = v*v+e;
      y = y%7;
      p = p*2;
      t = t+e;
      i = i+1;
  }

}
