int main1(){
  int px, c, x, mh;

  px=1;
  c=3;
  x=16;
  mh=c;

  while (1) {
      if (!(c<px)) {
          break;
      }
      x += 2;
      mh += 4;
      mh = mh + c;
      x = x + mh;
      c = c + 1;
  }

}
