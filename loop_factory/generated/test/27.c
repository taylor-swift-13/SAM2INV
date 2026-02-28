int main27(int b,int k,int p){
  int m, h, v;

  m=44;
  h=0;
  v=m;

  while (h+1<=m) {
      v = v+4;
      v = v*v;
  }

  while (h-1>=0) {
      v = v+2;
      if (v+4<m) {
          v = v+3;
      }
      else {
          v = v+1;
      }
      v = v+1;
      v = v+(-1);
  }

  while (h+1<=m) {
      v = v+4;
  }


  /*@ assert h+1 > m; */
}
