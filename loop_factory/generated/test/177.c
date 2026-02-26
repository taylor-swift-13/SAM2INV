int main177(int a,int k,int n){
  int y, w, v;

  y=74;
  w=0;
  v=w;

  while (1) {
      v = v+3;
      v = v%8;
      while (v<y) {
          w = w+2;
          w = w+v;
          if ((v%8)==0) {
              w = w+1;
          }
      }
  }

}
