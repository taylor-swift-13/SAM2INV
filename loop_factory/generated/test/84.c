int main84(int a,int n,int q){
  int m, z, v;

  m=10;
  z=m;
  v=3;

  while (z-2>=0) {
      v = v+4;
      v = v-v;
      if ((z%6)==0) {
          v = v+z;
      }
  }

  while (1) {
      z = z+3;
      if (v+5<=a+m) {
          z = z*2;
      }
      if (z+3<m) {
          z = z+z;
      }
      z = z*z;
  }


  /*@ assert \false; */
}
