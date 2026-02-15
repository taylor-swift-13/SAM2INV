int main6(int m,int n,int p){
  int x, y, z, z1, w, p1;

  x=n;
  y=p;
  z=0;
  z1=0;
  w=0;
  p1=0;

  while (y!=0) {
      if (y%2==1) {
          z = z+x;
          y = y-1;
      }
      x = 2*x;
      y = y/2;
  }

  while (n>0) {
      z1 = z1+p*p;
      w = w+m*m;
      p1 = p1+p*m;
      n = n-1;
  }

}
