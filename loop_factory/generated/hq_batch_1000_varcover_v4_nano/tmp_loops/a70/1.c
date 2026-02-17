int main1(int a,int m,int n,int q){
  int l, i, v, z, t, u, r, p;

  l=(m%29)+15;
  i=0;
  v=-3;
  z=-6;
  t=a;
  u=6;
  r=-2;
  p=i;

  while (i<l) {
      v = v+5;
      t = t+2;
      u = u+i;
      if (i+3<=m+l) {
          v = v-u;
      }
      else {
          v = v+t;
      }
      i = i+1;
  }

}
