int main1(int b,int k,int m,int p){
  int l, i, v, j, c, n, z, u, h;

  l=m+5;
  i=1;
  v=3;
  j=-2;
  c=i;
  n=-8;
  z=m;
  u=5;
  h=-1;

  while (i<l) {
      v = v*2;
      j = j+v;
      c = c%8;
      u = u+z;
      u = u*j;
      if (i+1<=c+l) {
          h = h*(-1);
      }
      i = i*2;
  }

}
