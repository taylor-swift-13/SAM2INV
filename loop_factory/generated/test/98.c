int main98(int m,int n,int q){
  int z, u, y;

  z=(m%7)+7;
  u=0;
  y=q;

  while (u+1<=z) {
      y = y+2;
      y = y*y;
  }

  while (z-1>=0) {
      u = u+2;
      if (y<m+3) {
          u = u-u;
      }
      if (z+6<=u+y) {
          u = u-u;
      }
      else {
          u = u+u;
      }
      u = u+z;
  }

  while (1) {
      u = u+u;
      u = u+y;
      y = y+1;
  }

}
