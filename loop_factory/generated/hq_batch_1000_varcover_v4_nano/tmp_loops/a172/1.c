int main1(int a,int b,int k,int m){
  int l, i, v, u, y, g, p, t;

  l=m;
  i=1;
  v=a;
  u=-8;
  y=b;
  g=l;
  p=m;
  t=-1;

  while (i<l) {
      v = v*3+3;
      u = u*v+3;
      y = y%5;
      y = y*y+p;
      v = v-2;
      y = y%4;
      i = i*3;
  }

}
