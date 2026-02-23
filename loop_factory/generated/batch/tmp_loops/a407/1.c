int main1(int b,int p){
  int u, v, e, n;

  u=p-7;
  v=0;
  e=u;
  n=3;

  while (e!=0&&n!=0) {
      if (e>n) {
          e = e-n;
      }
      else {
          n = n-e;
      }
  }

}
