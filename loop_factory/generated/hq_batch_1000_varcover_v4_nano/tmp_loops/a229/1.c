int main1(int a,int b,int n,int q){
  int l, i, v, z, h, e;

  l=(q%8)+14;
  i=l;
  v=b;
  z=a;
  h=5;
  e=-1;

  while (i>0) {
      v = v*2;
      z = z/2;
      h = h*e;
      if (v+6<l) {
          v = v*v+e;
      }
      e = e*e+z;
      e = z*z;
      z = z*2;
      i = i-1;
  }

}
