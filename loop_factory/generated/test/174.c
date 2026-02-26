int main174(int b,int m,int p){
  int f, k, c, v, y;

  f=12;
  k=0;
  c=4;
  v=f;
  y=b;

  while (k<=f-2) {
      if (c+5<=f) {
          c = c+5;
      }
      else {
          c = f;
      }
  }

  while (y<f) {
      k = c;
      c = c+1;
      c = c+3;
      k = k+4;
      if ((y%7)==0) {
          c = c+f;
      }
  }

}
