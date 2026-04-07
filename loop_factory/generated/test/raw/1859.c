int main1(int c,int g){
  int xn, f4, w1g, xeh, vv, bbl4, r, l4j, lu, p8f;

  xn=39;
  f4=0;
  w1g=f4;
  xeh=-2;
  vv=c;
  bbl4=c+5;
  r=-2;
  l4j=f4;
  lu=0;
  p8f=0;

  while (1) {
      if (!(f4+1<=xn)) {
          break;
      }
      if (f4%6==3) {
          w1g++;
      }
      else {
          xeh++;
      }
      if (f4%6==4) {
          vv += 1;
      }
      else {
      }
      p8f = (p8f+vv)%4;
      bbl4 = (xeh)+(bbl4);
      r = r + w1g;
      l4j = (l4j+w1g)%2;
      bbl4 += 1;
      xn = (f4+1)-1;
      if (r+3<xn) {
          lu = lu + 1;
      }
      else {
          bbl4 += 1;
      }
  }

}
