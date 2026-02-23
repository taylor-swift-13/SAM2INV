int main1(int b,int p){
  int h, c, y, k;

  h=b;
  c=h;
  y=h;
  k=6;

  while (y!=0&&k!=0) {
      if (y>k) {
          y = y-k;
      }
      else {
          k = k-y;
      }
      k = k+k;
      k = k+y;
  }

}
