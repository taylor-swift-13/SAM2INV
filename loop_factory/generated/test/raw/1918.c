int main1(){
  int v4, j9, ba0, h9p, fz, yy, r1k6, rq;

  v4=45;
  j9=0;
  ba0=8;
  h9p=16;
  fz=0;
  yy=5;
  r1k6=j9;
  rq=2;

  while (1) {
      if (!(j9<v4)) {
          break;
      }
      if (!(fz!=0)) {
          ba0--;
          h9p = h9p + 1;
          fz = 0;
      }
      else {
          ba0 = ba0 + 1;
          h9p--;
          fz = 1;
      }
      j9++;
      if (rq+3<v4) {
          rq += yy;
      }
      yy = yy+(j9%2);
      r1k6 = r1k6 + rq;
      rq += yy;
  }

}
