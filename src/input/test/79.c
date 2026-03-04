int main79(int b,int k,int m){
  int n, u, e;

  n=58;
  u=0;
  e=1;

  while (u<=n-1) {
      if (e==1) {
          e = 2;
      }
      else {
          if (e==2) {
              e = 1;
          }
      }
      e = e*e;
  }

}
