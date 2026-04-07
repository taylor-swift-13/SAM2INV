int main1(){
  int b2, bx, ja, d80, xma2, w, h, b, rd;

  b2=189;
  bx=0;
  ja=6;
  d80=0;
  xma2=3;
  w=bx;
  h=b2;
  b=b2;
  rd=4;

  while (1) {
      if (!(bx<b2)) {
          break;
      }
      if (!(!(bx%2==0))) {
          if (ja>0) {
              ja = ja - 1;
              d80 = d80 + 1;
          }
      }
      else {
          if (d80>0) {
              d80--;
              ja += 1;
          }
      }
      b = b + ja;
      h += 1;
      bx += 1;
      w += d80;
      rd = rd+(bx%2);
      xma2 = xma2 + 3;
      w += xma2;
  }

}
