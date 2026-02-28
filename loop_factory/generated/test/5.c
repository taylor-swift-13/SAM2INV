int main5(int b,int k,int p){
  int h, q, y, n;

  h=68;
  q=2;
  y=5;
  n=h;

  while (q<h) {
      n = n+y;
      y = y+n;
      n = n+n;
  }


  /*@ assert q >= h; */
}
