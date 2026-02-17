int main1(int a,int m,int q){
  int l, i, v, z, j, u, d;

  l=(m%7)+13;
  i=l;
  v=-2;
  z=a;
  j=i;
  u=i;
  d=q;

  while (v!=0&&z!=0) {
      if (v>z) {
          v = v-z;
      }
      else {
          z = z-v;
      }
  }

}
