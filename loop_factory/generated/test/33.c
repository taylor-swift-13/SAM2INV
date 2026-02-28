int main33(int b,int m,int p){
  int r, i, v, l, a;

  r=p;
  i=0;
  v=b;
  l=-3;
  a=3;

  while (i<r) {
      if (a<r) {
          l = v;
      }
      v = v+1;
      v = v*v+v;
      if (b*b<=r+6) {
          l = l*2;
      }
  }


  /*@ assert i >= r; */
}
