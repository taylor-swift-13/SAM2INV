int main1(int a,int m,int n,int p){
  int l, i, v, d, z;

  l=(p%11)+10;
  i=0;
  v=a;
  d=a;
  z=m;

  while (i<l) {
      v = v+3;
      z = z+1;
      if (i+2<=n+l) {
          z = z+3;
      }
      i = i+1;
  }

}
