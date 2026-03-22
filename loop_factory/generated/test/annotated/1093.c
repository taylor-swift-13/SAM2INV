int main1(int l,int x){
  int jy6, kav, qb, z9, k, o2;
  jy6=11;
  kav=0;
  qb=0;
  z9=0;
  k=0;
  o2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == \at(l, Pre) + kav*(kav+1)/2;
  loop invariant qb == 0;
  loop invariant o2 >= 0;
  loop invariant kav >= 0;
  loop invariant kav <= jy6;
  loop invariant z9 >= 0;
  loop invariant k >= 0;
  loop assigns kav, l, o2, k, z9, qb;
*/
while (kav<=jy6-1) {
      if (!(!(kav%7==0))) {
          if (kav%9==0) {
              k += 1;
          }
          else {
              if (kav%7==0) {
                  z9 += 1;
              }
              else {
                  qb++;
              }
          }
      }
      else {
          o2 += 1;
      }
      kav++;
      l += kav;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= z9;
  loop invariant 0 <= o2;
  loop invariant 0 <= kav;
  loop invariant 0 <= k;
  loop invariant x >= \at(x, Pre);
  loop invariant ((x - \at(x, Pre)) % 3) == 0;
  loop assigns k, kav, z9, o2, x;
*/
while (1) {
      if (!(z9<=qb-1)) {
          break;
      }
      k = k + z9;
      kav = kav + k;
      z9 += 1;
      o2 += 2;
      x = x + 3;
      o2 += 1;
  }
}