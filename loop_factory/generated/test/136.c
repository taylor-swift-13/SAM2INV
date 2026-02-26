int main136(int b,int k,int n){
  int d, h, v, j, e;

  d=n;
  h=d;
  v=b;
  j=-8;
  e=h;

  while (h>0) {
      v = v+1;
      j = j+v;
      v = v*4;
      j = j/4;
      j = j%5;
  }

}
