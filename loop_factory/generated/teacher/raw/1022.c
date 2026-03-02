int main1(int m,int n){
  int c, u, g, v;

  c=n+13;
  u=0;
  g=-2;
  v=m;

  while (1) {
      if (u>=c) {
          break;
      }
      g = g+2;
      u = u+1;
      g = g*2+5;
  }

}
