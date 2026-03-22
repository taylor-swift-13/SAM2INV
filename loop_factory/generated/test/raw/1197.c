int main1(){
  int b7x, l7, sq, d2p2, yp, dh, a6;

  b7x=1;
  l7=1;
  sq=-1;
  d2p2=-5;
  yp=l7;
  dh=b7x;
  a6=b7x;

  while (sq!=d2p2) {
      if (sq>d2p2) {
          sq -= d2p2;
          dh = dh + yp;
      }
      else {
          d2p2 -= sq;
          yp += dh;
      }
      a6 = a6 + l7;
  }

}
