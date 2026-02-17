int main1(int b,int k,int m,int n){
  int l, i, v, y, c, e, h, s, u;

  l=(m%8)+5;
  i=1;
  v=i;
  y=m;
  c=n;
  e=l;
  h=n;
  s=m;
  u=l;

  while (v!=0&&y!=0) {
      if (v>y) {
          v = v-y;
      }
      else {
          y = y-v;
      }
      v = v*4;
      y = y/4;
  }

}
