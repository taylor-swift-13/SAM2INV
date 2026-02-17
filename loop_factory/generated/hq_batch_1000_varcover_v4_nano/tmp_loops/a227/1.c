int main1(int b,int k,int m,int q){
  int l, i, v, z, w, s, j, g, u, d;

  l=m+23;
  i=0;
  v=-2;
  z=k;
  w=m;
  s=q;
  j=i;
  g=2;
  u=q;
  d=m;

  while (v!=0&&z!=0) {
      if (v>z) {
          v = v-z;
      }
      else {
          z = z-v;
      }
      s = s*s+v;
      v = v%5;
      z = z*z+d;
      s = s*s+v;
      d = d*d+z;
      d = d%9;
      s = s*s+j;
  }

}
