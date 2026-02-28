int main22(int m,int p,int q){
  int z, u, v, e;

  z=69;
  u=0;
  v=u;
  e=q;

  while (u<z) {
      if (v+2<=z) {
          v = v+2;
      }
      else {
          v = z;
      }
      v = v+1;
  }

  while (v+2<=u) {
      z = z+3;
  }


  /*@ assert v+2 > u; */
}
