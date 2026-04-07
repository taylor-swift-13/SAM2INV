int main1(){
  int fj, fek1, z3, xh, h, jdr, si, fe, y, qb1h;

  fj=18;
  fek1=1;
  z3=0;
  xh=1;
  h=0;
  jdr=fek1;
  si=0;
  fe=-6;
  y=-5;
  qb1h=5;

  while (1) {
      if (!(z3>=0&&z3<3)) {
          break;
      }
      if (z3==0&&xh>=fj) {
          z3 = 3;
      }
      else {
          if (z3==1&&h<xh) {
              jdr = jdr+xh-h;
              h += 1;
          }
          else {
              if (z3==1&&h>=xh) {
                  z3 = 2;
              }
              else {
                  if (z3==2) {
                      xh += 1;
                      z3 = 0;
                  }
              }
          }
      }
      y += xh;
      si++;
      fe += si;
      fe = si-fe;
      qb1h = qb1h + fek1;
  }

}
