int main1(int n,int q){
  int u, v, c, i;

  u=50;
  v=u;
  c=q;
  i=n;

  while (1) {
      if (v>=u) {
          break;
      }
      c = c+2;
      v = v+1;
      c = c+i+i;
  }

}
