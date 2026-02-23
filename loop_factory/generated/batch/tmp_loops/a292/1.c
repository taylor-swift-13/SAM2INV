int main1(int b,int k){
  int y, u, x, r;

  y=61;
  u=y;
  x=b;
  r=3;

  while (x!=0&&r!=0) {
      if (x>r) {
          x = x-r;
      }
      else {
          r = r-x;
      }
  }

}
