int main1(){
  int qx, y9, r1, ri, d, lrs;

  qx=79;
  y9=0;
  r1=-6;
  ri=y9;
  d=y9;
  lrs=y9;

  while (1) {
      ri = ((r1%6))+(ri);
      d = d+d+lrs;
      y9++;
      r1 = r1*4+4;
      if (y9>=qx) {
          break;
      }
  }

}
