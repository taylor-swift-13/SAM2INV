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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mlys == -8 + 2*zzpw;
  loop invariant (zzpw % 4 == 0) ==> lgr == 6*(zzpw/4);
  loop invariant (zzpw % 4 == 1) ==> lgr == 6*(zzpw/4) + 1;
  loop invariant (zzpw % 4 == 2) ==> lgr == 6*(zzpw/4) + 3;
  loop invariant (zzpw % 4 == 3) ==> lgr == 6*(zzpw/4) + 6;
  loop invariant 0 <= q8;
  loop invariant 0 <= x9a9;
  loop invariant 0 <= aj;
  loop invariant 0 <= iy;
  loop invariant 0 <= lgr;
  loop invariant 0 <= cmz;
  loop invariant cmz <= 3*zzpw*(zzpw+1)/2;
  loop invariant q8 + x9a9 + aj + iy == zzpw;
  loop invariant 0 <= zzpw <= cw + 1;
  loop assigns q8, x9a9, aj, iy, zzpw, lgr, mlys, cmz;
*/
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