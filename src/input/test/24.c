int main24(int a,int k,int m){
  int x, z, i, v;

  x=m+17;
  z=0;
  i=0;
  v=5;

  while (i<x) {
      i = i+3;
      i = i*3+5;
      v = v*i+5;
      v = v%3;
      i = i*2;
  }

}
