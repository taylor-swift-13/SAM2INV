int main44(int a,int b,int n){
  int z, v, q, y;

  z=a;
  v=z;
  q=b;
  y=2;

  while (v>=4) {
      q = q*2;
      y = y/2;
  }

  while (v>0) {
      q = q*q+q;
      q = q%4;
      v = v-1;
      while (q<v) {
          z = z+1;
          y = y+1;
          z = z*z+z;
          z = z%6;
      }
  }

}
