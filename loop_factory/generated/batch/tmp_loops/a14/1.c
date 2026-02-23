int main1(int a,int k){
  int x, t, n, h;

  x=(a%13)+18;
  t=1;
  n=a;
  h=0;

  while (t*2<=x) {
      if (n+3<=x) {
          n = n+3;
      }
      else {
          n = x;
      }
      n = n*4+2;
      h = h*n+2;
  }

}
