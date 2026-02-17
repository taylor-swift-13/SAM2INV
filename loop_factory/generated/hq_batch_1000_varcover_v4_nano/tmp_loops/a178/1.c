int main1(int a,int m,int p,int q){
  int l, i, v, y, g, c, k, t;

  l=q+22;
  i=0;
  v=8;
  y=-5;
  g=l;
  c=q;
  k=4;
  t=l;

  while (i<l) {
      v = v*4+3;
      y = y*v+3;
      v = v+i;
      y = y*y;
      g = g+v*y;
      if ((i%7)==0) {
          k = k*2;
      }
      k = k*c;
  }

}
