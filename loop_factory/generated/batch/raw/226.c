int main1(int b,int n){
  int k, v, z, s;

  k=21;
  v=0;
  z=k;
  s=k;

  while (v<k) {
      if (v<k/2) {
          z = z+s;
      }
      else {
          z = z*s;
      }
      z = z*2+1;
  }

}
