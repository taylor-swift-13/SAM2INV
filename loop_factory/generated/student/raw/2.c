int main1(int a,int k){
  int r, u, v, y;

  r=44;
  u=r;
  v=k;
  y=u;

  while (1) {
      if (u>=r) {
          break;
      }
      v = v+1;
      u = u+1;
      y = y+y;
      y = y+v;
  }

}
