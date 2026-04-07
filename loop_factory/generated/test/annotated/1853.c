int main1(int c,int f){
  int lvs, moir, x, x2, fj, mau, qqn9, kd;
  lvs=59;
  moir=0;
  x=0;
  x2=0;
  fj=0;
  mau=0;
  qqn9=0;
  kd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= moir <= lvs;
  loop invariant f == \at(f, Pre) + moir*(moir+1)/2;
  loop invariant fj == ((moir-1)/9) - ((moir-1)/45);
  loop invariant 0 <= x2;
  loop invariant 0 <= x <= moir;
  loop invariant mau == 0;
  loop invariant 0 <= kd <= 8*moir;
  loop invariant qqn9 == ((moir + 1) / 2) % 2;
  loop invariant (moir == 0) ==> (x2 == 0);
  loop assigns c, f, kd, moir, qqn9, x, x2, fj, mau;
*/
while (moir<lvs) {
      if (!(!(moir%9==0))) {
          if (moir%5==0) {
              x2 += 1;
          }
          else {
              if (moir%3==0) {
                  fj++;
              }
              else {
                  if (1) {
                      mau += 1;
                  }
              }
          }
      }
      else {
          x = x + 1;
      }
      moir++;
      kd = kd+moir%9;
      f = f + moir;
      c = (c+fj)%8;
      qqn9 = (qqn9+moir)%2;
  }
}