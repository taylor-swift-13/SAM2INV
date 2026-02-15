int main3(int a,int n,int q){
  int x, y, z, z1, w, p;

  x=a;
  y=q;
  z=0;
  z1=0;
  w=0;
  p=0;

  while (y!=0) {
      if (y%2==1) {
          z = z+x;
          y = y-1;
      }
      x = 2*x;
      y = y/2;
  }

  while (a>0) {
      z1 = z1+n*n;
      w = w+q*q;
      p = p+n*q;
      a = a-1;
  }

}
