int main1(int b,int k,int p,int q){
  int l, i, v, c, n, e, r, x;

  l=45;
  i=l;
  v=-4;
  c=b;
  n=p;
  e=-8;
  r=-4;
  x=-3;

  while (i>0) {
      v = v*4+4;
      c = c*v+4;
      r = r%4;
      x = x*n;
      x = c*c;
      i = i/2;
  }

}
