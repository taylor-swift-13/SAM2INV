int main95(int n,int p,int q){
  int y, o, z;

  y=60;
  o=0;
  z=p;

  while (o<y) {
      z = z+3;
      z = z*z+z;
      if (n*n<=y+6) {
          z = z*z+z;
      }
      else {
          z = z*2;
      }
      if (z+3<y) {
          z = z+z;
      }
  }


  /*@ assert o >= y; */
}
