int main1(){
  int h9k, k, wnyx, y, o7, jfy, iw, ov8h;

  h9k=1*5;
  k=h9k+2;
  wnyx=(1%35)+15;
  y=(1%35)+15;
  o7=1;
  jfy=0;
  iw=0;
  ov8h=1;

  while (wnyx!=y) {
      if (wnyx>y) {
          wnyx = wnyx - y;
          o7 = o7 - jfy;
          iw = iw - ov8h;
      }
      else {
          y -= wnyx;
          jfy -= o7;
          ov8h -= iw;
      }
      o7 = o7 + k;
  }

}
