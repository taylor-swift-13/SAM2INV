int main1(int x,int d){
  int x7, xg, y, eg;

  x7=(x%27)+15;
  xg=0;
  y=5;
  eg=0;

  while (xg<=x7-1) {
      eg = xg%5;
      if (xg>=y) {
          y = (xg-y)%5;
          y = y+eg-y;
      }
      else {
          y += eg;
      }
      xg++;
      x = x+(xg%2);
  }

}
