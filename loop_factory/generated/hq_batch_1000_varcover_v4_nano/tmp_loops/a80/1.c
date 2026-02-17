int main1(int a,int b,int n,int q){
  int l, i, v, o, z, m, c, y;

  l=b+8;
  i=0;
  v=2;
  o=a;
  z=a;
  m=-5;
  c=n;
  y=n;

  while (i<l) {
      v = v*3+4;
      o = o*v+4;
      v = v+o;
      o = o+z;
      z = z+4;
      v = v*v+y;
      if ((i%7)==0) {
          y = m*m;
      }
  }

}
