int main1(int a,int b,int n,int p){
  int l, i, v, z, x, u, q;

  l=b;
  i=0;
  v=p;
  z=b;
  x=p;
  u=b;
  q=a;

  while (i<l) {
      v = v+i;
      z = z*z;
      x = x+v*z;
      z = z*z+u;
      z = z*z+v;
      v = x*x;
      i = i+2;
  }

}
