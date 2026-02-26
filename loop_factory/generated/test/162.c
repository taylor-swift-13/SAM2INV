int main162(int k,int m,int q){
  int l, u, z;

  l=q;
  u=l;
  z=q;

  while (u-2>=0) {
      z = z+2;
      if ((u%7)==0) {
          z = z+u;
      }
      else {
          z = z*2;
      }
      if ((u%6)==0) {
          z = z*z+z;
      }
      z = z*z;
  }

}
