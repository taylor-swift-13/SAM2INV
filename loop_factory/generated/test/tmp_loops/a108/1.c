int main1(int m,int n){
  int l, i, v, z;

  l=n+23;
  i=0;
  v=2;
  z=m;

  while (i<l) {
      v = v+1;
      z = z+1;
  }

  while (l<i) {
      v = v+z+z;
      l = l+1;
  }

}
