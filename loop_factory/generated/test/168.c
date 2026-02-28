int main168(int k,int m,int q){
  int h, w, v, x;

  h=58;
  w=0;
  v=h;
  x=h;

  while (v<h) {
      if (v<h) {
          v = v+1;
      }
  }

  while (1) {
      if (x>=h) {
          break;
      }
      v = v+3;
      x = x+1;
      v = v*4;
      w = w/4;
  }


  /*@ assert (x>=h); */
}
