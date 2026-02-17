int main1(int a,int k,int m,int n){
  int l, i, v, y, c, g, u, e;

  l=32;
  i=1;
  v=-5;
  y=4;
  c=m;
  g=a;
  u=-4;
  e=m;

  while (i<l) {
      g = g*g+v;
      v = v%5;
      u = c*c;
      c = c*u;
      u = y*y;
      u = u*2;
      i = i*3;
  }

}
