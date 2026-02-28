int main65(int a,int m,int p){
  int z, u, v;

  z=a+18;
  u=0;
  v=z;

  while (u<=z-1) {
      v = v+4;
      if (v+4<z) {
          v = v+1;
      }
      else {
          v = v-v;
      }
  }


  /*@ assert u > z-1; */
}
