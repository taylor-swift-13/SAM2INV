int main59(int b,int k,int p){
  int w, q, v, c, g;

  w=b-1;
  q=0;
  v=p;
  c=2;
  g=k;

  while (1) {
      if (v+2<=w) {
          v = v+2;
      }
      else {
          v = w;
      }
      while (q>3) {
          c = c+2;
          v = v+c;
          w = w+v;
          c = c*2;
      }
  }

}
