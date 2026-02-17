int main1(int b,int k,int n,int q){
  int l, i, v, z, h, d;

  l=q+18;
  i=1;
  v=b;
  z=i;
  h=l;
  d=-6;

  while (i<l) {
      if (v+4<=l) {
          v = v+4;
      }
      else {
          v = l;
      }
      v = v+i;
      z = z*z;
      h = h+v*z;
      h = h%2;
      v = v*d;
      z = z*z+h;
      v = v*v+z;
  }

}
