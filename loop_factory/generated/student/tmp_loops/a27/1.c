int main1(int k,int p){
  int s, u, z, v;

  s=48;
  u=s+1;
  z=3;
  v=p;

  while (u>0) {
      z = z*3;
      v = v/3;
      z = z*3+2;
      v = v*z+2;
  }

}
