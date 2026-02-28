int main157(int m,int n,int q){
  int t, i, v, j;

  t=m-5;
  i=0;
  v=2;
  j=i;

  while (i<=t-1) {
      if (i<t/2) {
          v = v+j;
      }
      else {
          v = v+1;
      }
      v = v+j+j;
      v = v+1;
      j = j+5;
  }


  /*@ assert i > t-1; */
}
