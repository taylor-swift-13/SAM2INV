int main1(int a,int m){
  int t, x, q, u;

  t=48;
  x=0;
  q=-4;
  u=x;

  while (1) {
      if (x>=t) {
          break;
      }
      q = q+2;
      x = x+1;
      q = q+2;
      u = u+q;
  }

}
