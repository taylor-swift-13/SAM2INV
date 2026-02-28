int main67(int a,int k,int q){
  int z, j, w;

  z=53;
  j=0;
  w=-1;

  while (1) {
      w = w+4;
      w = w+w;
      while (w<=j-5) {
          z = z+2;
          if (z*z<=j+5) {
              z = z*z+z;
          }
          z = z*z+z;
      }
      while (z<=j-1) {
          w = w+3;
          if (z+5<=w+j) {
              w = w+1;
          }
          else {
              w = w-w;
          }
          w = w+z;
      }
  }


  /*@ assert z > j-1; */
}
