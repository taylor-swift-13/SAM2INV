int main1(int b,int n){
  int k, v, z, s;

  k=21;
  v=0;
  z=k;
  s=k;

  while (z!=0&&s!=0) {
      if (z>s) {
          z = z-s;
      }
      else {
          s = s-z;
      }
      s = s+s;
  }

}
