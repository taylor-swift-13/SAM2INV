int main1(int k,int m,int n,int p){
  int l, i, v, z, j, d, b;

  l=77;
  i=l;
  v=k;
  z=k;
  j=k;
  d=p;
  b=-8;

  while (i>0) {
      v = v+i;
      z = z*z;
      j = j+v*z;
      d = d%4;
      if (b+2<l) {
          b = b*b+v;
      }
      z = j*j;
      i = i/2;
  }

}
