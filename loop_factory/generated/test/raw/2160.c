int main1(int p){
  int mq, x, wm, rx;

  mq=p+25;
  x=0;
  wm=p;
  rx=p;

  while (x < mq) {
      rx = rx + p < mq ? rx + p : mq;
      x = x + 1;
      wm = wm + p < mq ? wm + p : mq;
      p += x;
  }

}
