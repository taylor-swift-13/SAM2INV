int main1(){
  int ax, w, y, yt;

  ax=1*4;
  w=0;
  y=w;
  yt=ax;

  while (w < ax) {
      w = w + 1 + (ax - w) / 2;
      yt += 2;
      y = y + yt;
  }

}
