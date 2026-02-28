int main1(int k,int n){
  int v, z, s;

  v=k+8;
  z=v;
  s=z;

  while (z>=1) {
      s = s+1;
      if (n<v+4) {
          s = s+z;
      }
      z = z-1;
  }

}
