int main52(int k,int m,int p){
  int b, j, f, r, i;

  b=k+6;
  j=b;
  f=b;
  r=-5;
  i=j;

  while (j>=1) {
      if (i<=r) {
          r = i;
      }
      f = f+1;
      f = f+3;
      i = i+3;
      f = i-f;
      while (i<b) {
          f = f*4+1;
          r = r*f+1;
          f = f+i;
      }
  }


  /*@ assert i >= b; */
}
