int main1(int b,int n){
  int p, u, v;

  p=n-3;
  u=p;
  v=p;

  while (u-1>=0) {
      v = v+2;
      v = v*v;
      if (n*n<=p+4) {
          v = v*v+v;
      }
      else {
          v = v*v+v;
      }
  }

}
