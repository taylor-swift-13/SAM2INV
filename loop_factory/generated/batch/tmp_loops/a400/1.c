int main1(int a,int b){
  int n, u, g, v;

  n=(a%37)+9;
  u=n;
  g=n;
  v=-1;

  while (u>=1) {
      if (g+6<=n) {
          g = g+6;
      }
      else {
          g = n;
      }
  }

}
