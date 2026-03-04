int main68(int a,int b,int q){
  int n, u, l;

  n=37;
  u=0;
  l=n;

  while (1) {
      l = l+u;
      if (b*b<=n+3) {
          l = l%9;
      }
      else {
          l = l+l;
      }
      u = u+1;
  }

}
