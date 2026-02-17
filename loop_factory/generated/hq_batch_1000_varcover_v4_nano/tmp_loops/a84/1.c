int main1(int a,int b,int m,int q){
  int l, i, v, h, z, e;

  l=(b%38)+19;
  i=0;
  v=i;
  h=q;
  z=b;
  e=l;

  while (i<l) {
      v = v*4;
      h = h/4;
      v = v*z;
      e = e*h;
      if (i+3<=a+l) {
          z = z*h;
      }
      z = z*z+h;
      i = i+4;
  }

}
