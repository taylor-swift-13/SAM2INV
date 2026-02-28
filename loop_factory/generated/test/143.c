int main143(int a,int b,int p){
  int k, n, e, v;

  k=(p%10)+10;
  n=2;
  e=-2;
  v=b;

  while (1) {
      e = e*3+3;
      v = v*e+3;
      e = e*2;
      while (v<e) {
          if (v<e) {
              v = v+1;
          }
          v = v*3;
          k = k/3;
          v = v%6;
          k = k%8;
      }
  }


  /*@ assert v >= e; */
}
