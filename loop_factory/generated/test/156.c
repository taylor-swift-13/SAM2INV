int main156(int b,int k,int n){
  int m, j, i;

  m=b;
  j=2;
  i=n;

  while (1) {
      i = i+3;
      i = i*i+i;
  }

  while (j<=i-5) {
      m = m+4;
      m = m+1;
  }


  /*@ assert j > i-5; */
}
