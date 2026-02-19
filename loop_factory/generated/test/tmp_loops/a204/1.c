int main1(int a,int n){
  int l, i, v, z;

  l=(n%8)+18;
  i=0;
  v=2;
  z=2;

  while (i<l) {
      v = v+z+z;
      v = v+1;
      i = i+1;
  }

  while (l>0) {
      i = i+1;
      l = l-1;
  }

}
