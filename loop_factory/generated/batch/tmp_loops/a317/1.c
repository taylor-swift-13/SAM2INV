int main1(int a,int q){
  int n, c, v, y;

  n=(a%36)+20;
  c=0;
  v=1;
  y=a;

  while (c+1<=n) {
      if (v+6<=n) {
          v = v+6;
      }
      else {
          v = n;
      }
  }

}
