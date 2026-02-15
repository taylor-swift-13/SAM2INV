int main14(int k,int p,int q){
  int z, w, p1, x, y, z1;

  z=0;
  w=0;
  p1=0;
  x=p;
  y=k;
  z1=0;

  while (p>0) {
      z = z+q*q;
      w = w+k*k;
      p1 = p1+q*k;
      p = p-1;
  }

  while (y!=0) {
      if (y%2==1) {
          z1 = z1+x;
          y = y-1;
      }
      x = 2*x;
      y = y/2;
  }

}
