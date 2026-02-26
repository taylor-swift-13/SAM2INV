int main101(int a,int b,int p){
  int m, t, s;

  m=(a%15)+14;
  t=0;
  s=-1;

  while (t<m) {
      s = s+2;
  }

  while (t-3>=0) {
      m = m+3;
      m = m*2;
      if (m+4<s) {
          m = m*m;
      }
      else {
          m = m+t;
      }
  }

}
