int main1(){
  int k, l0, xy, hs, sx, kh, u, sh, jh;
  k=1*4;
  l0=k;
  xy=0;
  hs=1;
  sx=0;
  kh=k;
  u=k;
  sh=-5;
  jh=l0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l0 == k;
  loop invariant u == -16 - 4*sh;
  loop invariant u == jh;
  loop invariant xy == 0;
  loop invariant hs == 1;
  loop invariant sx == 0;
  loop invariant u >= 4;
  loop invariant k == 4;
  loop invariant kh >= 4;
  loop invariant k == 4 && l0 == 4 && hs >= 1 && sh <= -5 &&
                   sx >= 0 && sx <= hs &&
                   0 <= xy && xy <= 3 && u >= 4 && (u % 4) == 0 &&
                   jh >= 4 && kh >= 4;
  loop assigns xy, kh, sx, hs, jh, u, sh;
*/
while (xy>=0&&xy<3) {
      if (!(!(xy==0&&hs>=k))) {
          xy = 3;
      }
      else {
          if (xy==1&&sx<hs) {
              kh = kh+hs-sx;
              sx++;
          }
          else {
              if (xy==1&&sx>=hs) {
                  xy = 2;
              }
              else {
                  if (xy==2) {
                      hs = hs + 1;
                      xy = 0;
                  }
              }
          }
      }
      jh = jh + sx;
      u = u + 3;
      u = u + 1;
      sh--;
      jh += l0;
  }
}