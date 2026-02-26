int main1(int a,int n){
  int b, u, y, s;

  b=49;
  u=0;
  y=n;
  s=1;

  while (u+1<=b) {
      if (y+3<=b) {
          y = y+3;
      }
      else {
          y = b;
      }
      y = y+u;
  }

}
