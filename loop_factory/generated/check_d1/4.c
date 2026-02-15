int main4(int a,int k,int q){
  int x, y, z;

  x=a;
  y=q;
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
