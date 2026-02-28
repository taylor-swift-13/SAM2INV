int main38(int b,int m,int n){
  int z, g, r;

  z=(n%38)+19;
  g=2;
  r=z;

  while (g+1<=z) {
      r = r+4;
      r = r+g;
      if (r+1<z) {
          r = r-r;
      }
  }

  while (z-1>=0) {
      r = r+z;
      if ((z%4)==0) {
          r = r+6;
      }
      if (g<r+1) {
          r = r-r;
      }
      r = r+z;
      z = z-1;
      while (r<z) {
          g = g+2;
          if (r+6<=z+z) {
              g = g+g;
          }
      }
  }


  /*@ assert r >= z; */
}
