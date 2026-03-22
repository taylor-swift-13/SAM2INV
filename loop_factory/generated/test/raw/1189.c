int main1(){
  int wl, x0h, ve, farv, y;

  wl=1;
  x0h=(1%28)+8;
  ve=(1%22)+5;
  farv=0;
  y=0;

  while (ve!=0) {
      if (ve%2==1) {
          farv += x0h;
          ve--;
      }
      x0h = 2*x0h;
      ve = ve/2;
      y = y + wl;
  }

}
