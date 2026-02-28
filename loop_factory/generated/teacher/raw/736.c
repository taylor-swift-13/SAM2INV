int main1(int a,int b,int k,int n){
  int y, u, v, m, x;

  y=n+25;
  u=0;
  v=k;
  m=2;
  x=b;

  while (1) {
      if (v+3<=y) {
          v = v+3;
      }
      else {
          v = y;
      }
      m = m+x;
      x = x+v;
      x = v-x;
  }

}
