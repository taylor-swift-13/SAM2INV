int main1(int k,int m,int p,int q){
  int l, i, v, w, u, f, c;

  l=(k%8)+14;
  i=1;
  v=q;
  w=-2;
  u=6;
  f=q;
  c=p;

  while (i<l) {
      v = v+i;
      w = w*w;
      u = u+v*w;
      f = f-2;
      c = c%2;
      i = i*3;
  }

}
