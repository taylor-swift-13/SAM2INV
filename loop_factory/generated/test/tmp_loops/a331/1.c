int main1(int b,int m){
  int l, i, v, z;

  l=m;
  i=0;
  v=m;
  z=b;

  while (i<l) {
      v = v+1;
      z = z-1;
  }

  while (z<i) {
      l = l+z;
      l = l-l;
      z = z+1;
  }

}
