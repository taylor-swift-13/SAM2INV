int main12(int a,int b,int k){
  int x, y, z, x1, y1, c;

  x=b;
  y=a;
  z=0;
  x1=1;
  y1=a;
  c=1;

  while (y!=0) {
      if (y%2==1) {
          z = z+x;
          y = y-1;
      }
      x = 2*x;
      y = y/2;
      while (c<b) {
          c = c+1;
          x1 = x1*a+1;
          y1 = y1*a;
      }
  }

}
