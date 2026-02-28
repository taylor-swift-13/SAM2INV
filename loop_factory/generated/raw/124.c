int main124(int k,int m,int p){
  int v, b, l, c, y;

  v=p-8;
  b=0;
  l=v;
  c=-1;
  y=-5;

  while (l!=0&&c!=0) {
      if (l>c) {
          l = l-c;
      }
      else {
          c = c-l;
      }
      l = l+1;
      c = c-1;
      y = y+l;
      c = c+b;
  }

  while (1) {
      if (y>=c) {
          break;
      }
      l = l+3;
      y = y+1;
  }

  while (b>0) {
      v = v+c;
  }

}
