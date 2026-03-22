int main1(){
  int cw, zzpw, iy, q8, x9a9, aj, cmz, lgr, mlys;

  cw=166;
  zzpw=0;
  iy=0;
  q8=0;
  x9a9=0;
  aj=0;
  cmz=0;
  lgr=0;
  mlys=-8;

  while (zzpw<cw+(1%7)) {
      if (!(!(zzpw%11==0))) {
          if (zzpw%5==0) {
              q8++;
          }
          else {
              if (zzpw%4==0) {
                  x9a9++;
              }
              else {
                  if (1) {
                      aj += 1;
                  }
              }
          }
      }
      else {
          iy++;
      }
      zzpw++;
      lgr = lgr+zzpw%4;
      mlys += 2;
      cmz = cmz + lgr;
  }

}
