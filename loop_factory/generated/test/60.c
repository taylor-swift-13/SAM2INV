int main60(int a,int b,int q){
  int n, t, u;

  n=b-3;
  t=1;
  u=a;

  while (t*3<=n) {
      u = u+2;
      u = u*u+u;
  }

  while (t<n) {
      u = u+4;
      u = u*2;
      while (n<=u/2) {
          t = t+4;
          t = t%8;
      }
  }

}
