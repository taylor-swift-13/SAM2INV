int main14(int k,int n,int q){
  int c, t, m;

  c=k+3;
  t=0;
  m=1;

  while (t+3<=c) {
      if (m==1) {
          m = 2;
      }
      else {
          if (m==2) {
              m = 1;
          }
      }
      m = m*m+m;
      m = m*m;
  }

}
