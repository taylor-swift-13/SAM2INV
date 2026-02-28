int main176(int m,int n,int p){
  int h, e, w, r;

  h=p;
  e=h;
  w=m;
  r=8;

  while (w<h) {
      if (w<h) {
          w = w+1;
      }
      w = w*w+w;
      w = w%4;
  }


  /*@ assert w >= h; */
}
