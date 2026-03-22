int main1(){
  int jw, ws, d8, n, sb, o2r, dj;

  jw=0;
  ws=-3;
  d8=8;
  n=0;
  sb=jw;
  o2r=jw;
  dj=1+2;

  while (ws!=d8) {
      if (!(ws<=d8)) {
          d8 -= ws;
          n = n + sb;
      }
      else {
          ws -= d8;
          sb += n;
      }
      o2r = o2r + sb;
      dj = dj+(sb%8);
  }

}
