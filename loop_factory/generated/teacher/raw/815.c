int main1(int k,int q){
  int n, z, b, v;

  n=k;
  z=0;
  b=-2;
  v=k;

  while (1) {
      b = b+2;
      v = v+1;
      b = b+z;
      v = v+z;
      z = z+1;
  }

}
