int main178(int n,int p,int q){
  int h, k, x, v, w;

  h=68;
  k=h;
  x=-3;
  v=p;
  w=q;

  while (k>=3) {
      x = x+1;
      v = v+x;
      x = x+k;
      v = v*v;
      w = w+x*v;
  }

  while (w<h) {
      k = k*3;
      v = v/3;
  }


  /*@ assert w >= h; */
}
