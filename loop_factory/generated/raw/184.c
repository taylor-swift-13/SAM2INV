int main184(int a,int b,int n){
  int l, y, v, w;

  l=n+5;
  y=l;
  v=y;
  w=5;

  while (y>=1) {
      v = v+6;
      w = w+6;
      while (1) {
          v = v*v+v;
          v = v%9;
          y = y*v;
          if (v+2<l) {
              v = y+w;
          }
          w = w+1;
      }
      while (y<v) {
          if (y<v/2) {
              w = w+l;
          }
          else {
              w = w*l;
          }
          w = w*2;
          l = l/2;
      }
  }

}
