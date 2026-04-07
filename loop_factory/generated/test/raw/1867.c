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
