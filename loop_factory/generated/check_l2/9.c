int main9(int a,int k,int q){
  int x, y, z, x1, y1, z1;

  x=k;
  y=a;
  z=0;
  x1=k;
  y1=q;
  z1=0;

  while (y!=0) {
      if (y%2==1) {
          z = z+x;
          y = y-1;
      }
      x = 2*x;
      y = y/2;
      while (y1!=0) {
          if (y1%2==1) {
              z1 = z1+x1;
              y1 = y1-1;
          }
          x1 = 2*x1;
          y1 = y1/2;
      }
  }

}
