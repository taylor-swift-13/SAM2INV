int main47(int a,int m,int n){
  int c, e, v, l;

  c=9;
  e=0;
  v=0;
  l=e;

  while (e<=c-1) {
      e = e+1;
      while (1) {
          c = c*2;
          e = e/2;
          c = c*c+c;
          c = c%2;
      }
  }


  /*@ assert \false; */
}
