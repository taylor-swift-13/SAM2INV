int main1(int r,int y){
  int g, gvr, zr, h, m, yo, zp;

  g=(y%9)+8;
  gvr=0;
  zr=0;
  h=0;
  m=0;
  yo=0;
  zp=0;

  while (gvr<g+(y%7)) {
      if (gvr%11==0) {
          zr += 1;
      }
      else {
          if (gvr%5==0) {
              h += 1;
          }
          else {
              if (gvr%3==0) {
                  m++;
              }
              else {
                  if (1) {
                      yo++;
                  }
              }
          }
      }
      gvr += 1;
      zp = zp + 1;
      r = r + gvr;
      r += zp;
  }

}
