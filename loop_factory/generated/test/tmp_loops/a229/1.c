int main1(int a,int q){
  int l, i, v, z;

  l=65;
  i=1;
  v=0;
  z=q;

  while (i<l) {
      v = v+z+z;
      v = v+1;
      i = i*2;
  }

  while (l>0) {
      z = z+z;
      l = l-1;
  }

}
