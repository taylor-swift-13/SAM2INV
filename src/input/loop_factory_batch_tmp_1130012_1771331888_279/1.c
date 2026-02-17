int main1(int b,int n,int p,int q){
  int l, i, v, z, t, c;

  l=36;
  i=1;
  v=p;
  z=i;
  t=q;
  c=b;

  while (i<l) {
      v = v*4+3;
      z = z*v+3;
      if (i+6<=c+l) {
          v = v%6;
      }
      t = c*c;
      i = i*3;
  }

}
