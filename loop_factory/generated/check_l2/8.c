int main8(int a,int n,int q){
  int z, w, p, x, y, z1;

  z=0;
  w=0;
  p=0;
  x=n;
  y=q;
  z1=0;

  while (a>0) {
      z = z+q*q;
      w = w+n*n;
      p = p+q*n;
      a = a-1;
      while (y!=0) {
          if (y%2==1) {
              z1 = z1+x;
              y = y-1;
          }
          x = 2*x;
          y = y/2;
      }
  }

}
