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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= c;
  loop invariant c <= 3;
  loop invariant tm3 >= 1;
  loop invariant d8 >= 0;
  loop invariant d8 <= tm3;
  loop invariant f3 >= 9;
  loop invariant kw >= -5;
  loop invariant nv >= 0;
  loop invariant dkm == -4;
  loop invariant d93 == 0;
  loop invariant io == 9;
  loop invariant z == 5;
  loop assigns c, f3, d8, tm3, kw, nv, dkm;
*/
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