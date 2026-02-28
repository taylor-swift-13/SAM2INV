int main3(int m,int p,int q){
  int h, i, v, a, w;

  h=p+5;
  i=h;
  v=p;
  a=i;
  w=q;

  while (i>0) {
      v = v+1;
      a = a-1;
      v = v*4;
      while (i-1>=0) {
          if (v+3<=w) {
              v = v+3;
          }
          else {
              v = w;
          }
      }
      while (v>=1) {
          if (h<=w) {
              w = h;
          }
          a = a+1;
      }
  }


  /*@ assert v < 1; */
}
