int main15(int k,int m,int p){
  int x, y, z;

  x=p;
  y=m;
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
