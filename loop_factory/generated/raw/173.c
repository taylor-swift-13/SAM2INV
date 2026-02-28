int main173(int b,int k,int p){
  int s, y, v, u;

  s=(p%18)+17;
  y=s;
  v=1;
  u=-8;

  while (1) {
      if (y>=s) {
          break;
      }
      v = v+1;
      y = y+1;
      v = v+5;
      u = u+3;
      if (y+6<=u+s) {
          v = v+u;
      }
  }

  while (s-1>=0) {
      u = u*2+2;
      y = y*u+2;
      u = u*4;
  }

}
