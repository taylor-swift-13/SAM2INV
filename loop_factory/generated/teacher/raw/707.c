int main1(int a,int b,int m,int p){
  int r, t, g, v;

  r=m-7;
  t=r;
  g=t;
  v=r;

  while (1) {
      if (t>=r) {
          break;
      }
      g = g+1;
      t = t+1;
      g = g+v+v;
      g = g+1;
  }

}
