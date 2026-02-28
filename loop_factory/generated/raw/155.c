int main155(int m,int p,int q){
  int z, l, v;

  z=(m%36)+8;
  l=0;
  v=-4;

  while (l<=z-1) {
      v = v+3;
      v = v*v+v;
  }

  while (l>=4) {
      z = z+3;
      z = z*z;
  }

}
