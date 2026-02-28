int main1(int a,int b,int k,int m){
  int y, u, l, v, t, w;

  y=63;
  u=1;
  l=u;
  v=5;
  t=m;
  w=a;

  while (1) {
      v = v+l;
      v = v+t;
      t = t+l;
      if ((u%2)==0) {
          t = t+u;
      }
      else {
          v = v+u;
      }
  }

}
