int main196(int a,int k,int m){
  int b, j, o;

  b=m-4;
  j=4;
  o=j;

  while (j<=b-1) {
      o = o+3;
      o = o%7;
  }

  while (b<j) {
      o = o+2;
      o = o*o+o;
  }


  /*@ assert b >= j; */
}
