int main137(int m,int n,int q){
  int v, e, c, b, i;

  v=35;
  e=v;
  c=8;
  b=-5;
  i=v;

  while (e-1>=0) {
      c = c*c+c;
      c = c%8;
      e = e-1;
  }


  /*@ assert e-1 < 0; */
}
