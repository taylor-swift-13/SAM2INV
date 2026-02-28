int main10(int a,int k,int p){
  int b, c, v, y;

  b=71;
  c=b+6;
  v=6;
  y=a;

  while (c-b>0) {
      if (c<b/2) {
          v = v+y;
      }
      else {
          v = v*y;
      }
      v = v*4;
      y = y/4;
      if (k*k<=b+5) {
          y = y*v;
      }
  }


  /*@ assert c-b <= 0; */
}
