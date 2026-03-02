int main1(int a,int p){
  int s, t, v, z;

  s=a;
  t=s;
  v=s;
  z=3;

  while (v!=0&&z!=0) {
      if (v>z) {
          v = v-z;
      }
      else {
          z = z-v;
      }
      v = v+4;
      z = z+4;
      v = z-v;
  }

}
