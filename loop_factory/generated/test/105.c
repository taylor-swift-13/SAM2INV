int main105(int a,int m,int p){
  int x, c, w, l;

  x=61;
  c=0;
  w=0;
  l=x;

  while (1) {
      l = x-w;
      w = w+1;
  }

  while (1) {
      l = l+x;
      x = x+l;
  }


  /*@ assert \false; */
}
