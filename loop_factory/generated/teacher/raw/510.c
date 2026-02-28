int main1(int b,int m){
  int x, t, y, o;

  x=b;
  t=0;
  y=-2;
  o=t;

  while (y!=0&&o!=0) {
      if (y>o) {
          y = y-o;
      }
      else {
          o = o-y;
      }
  }

}
