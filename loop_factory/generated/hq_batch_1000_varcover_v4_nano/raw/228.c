int main1(int m,int n,int p){
  int l, i, v, z;

  l=64;
  i=0;
  v=-4;
  z=n;

  while (i<l) {
      v = v+3;
      z = z+v;
      z = z+z;
      v = v+6;
      i = i+1;
  }

}
