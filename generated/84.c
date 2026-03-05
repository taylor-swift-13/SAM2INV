int main84(int h,int w,int c){
  int l, eh, yis, r0, hd, djy, w1x;

  l=h+5;
  eh=1;
  yis=0;
  r0=0;
  hd=w;
  djy=c;
  w1x=eh;

  while (r0<l) {
      yis = (yis+1)%7;
      r0 = r0 + 1;
      c = (c+r0)%5;
      hd = hd+(yis%8);
      w1x = (w1x+yis)%4;
      djy += r0;
  }

}
