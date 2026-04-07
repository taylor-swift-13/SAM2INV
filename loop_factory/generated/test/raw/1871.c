int main1(){
  int io, d93, c, tm3, d8, f3, z, nv, kw, dkm;

  io=(1%28)+8;
  d93=0;
  c=0;
  tm3=1;
  d8=0;
  f3=io;
  z=5;
  nv=d93;
  kw=-5;
  dkm=-4;

  while (c>=0&&c<3) {
      if (!(!(c==0&&tm3>=io))) {
          c = 3;
      }
      else {
          if (c==1&&d8<tm3) {
              f3 = f3+tm3-d8;
              d8 = d8 + 1;
          }
          else {
              if (c==1&&d8>=tm3) {
                  c = 2;
              }
              else {
                  if (c==2) {
                      tm3 = tm3 + 1;
                      c = 0;
                  }
              }
          }
      }
      kw = kw + f3;
      nv = nv + 3;
      dkm = dkm+(d93%2);
      nv += kw;
      kw += z;
  }

}
