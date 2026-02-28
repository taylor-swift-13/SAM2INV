int main9(int b,int k,int q){
  int m, u, t, p, r;

  m=b-6;
  u=m;
  t=0;
  p=u;
  r=u;

  while (u-4>=0) {
      p = m-t;
      t = t+1;
      t = t+p+r;
  }

  while (t+4<=m) {
      r = r+3;
      r = r+1;
      p = p+r;
      r = r+t;
  }

  while (t<u) {
      if (t<u) {
          t = t+1;
      }
      t = t+1;
      p = p-1;
  }

}
