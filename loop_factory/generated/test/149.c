int main149(int b,int n,int p){
  int u, m, a;

  u=p+15;
  m=u+2;
  a=1;

  while (m>1) {
      a = a+4;
      if (a+2<u) {
          a = a*a+a;
      }
      else {
          a = a*a;
      }
      a = a*a;
  }

  while (u>0) {
      m = m+3;
      m = m*m;
  }

  while (a+1<=u) {
      m = m+2;
      m = m*2;
  }


  /*@ assert a+1 > u; */
}
