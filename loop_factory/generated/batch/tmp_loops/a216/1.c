int main1(int k,int n){
  int m, t, v, y;

  m=n+20;
  t=1;
  v=t;
  y=n;

  while (t<m) {
      if (v+4<=m) {
          v = v+4;
      }
      else {
          v = m;
      }
      v = v+t;
      y = y*y;
  }

}
