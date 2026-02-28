int main1(int a,int p){
  int s, t, v, z, n, i;

  s=a-9;
  t=0;
  v=p;
  z=p;
  n=p;
  i=-1;

  while (v!=0&&z!=0) {
      if (v>z) {
          v = v-z;
      }
      else {
          z = z-v;
      }
  }

}
