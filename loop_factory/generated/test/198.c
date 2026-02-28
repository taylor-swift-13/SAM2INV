int main198(int b,int k,int p){
  int c, w, v, r, g;

  c=b;
  w=0;
  v=-1;
  r=-6;
  g=8;

  while (w>=w) {
      v = v+10;
      r = r+10;
      v = v*2;
      r = r+v;
      g = g%5;
      while (g!=0&&w!=0) {
          if (g>w) {
              g = g-w;
          }
          else {
              w = w-g;
          }
          g = g+1;
      }
      while (1) {
          if (r>=v) {
              break;
          }
          c = c+3;
          r = r+1;
          w = w+w;
          w = w+c;
          c = c+w;
      }
  }


  /*@ assert (r>=v); */
}
