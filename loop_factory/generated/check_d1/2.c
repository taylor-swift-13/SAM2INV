int main2(int m,int p,int q){
  int x, y, z;

  x=q;
  y=p;
  z=0;

  while (y!=0) {
      if (y%2==1) {
          z = z+x;
          y = y-1;
      }
      x = 2*x;
      y = y/2;
  }

}
