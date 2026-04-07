int main1(int s){
  int t, t30, ndxi, kxd, myl3;
  t=s+13;
  t30=-3;
  ndxi=0;
  kxd=3;
  myl3=t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == \at(s, Pre) + 13;
  loop invariant kxd == 2*(myl3 - t) + 3;
  loop invariant ndxi == (myl3 - t) * (myl3 - t + 2);
  loop invariant t30 == -3 + ((myl3 - t) * (myl3 - t - 1) * (2*(myl3 - t) + 5)) / 6;
  loop invariant 0 <= (myl3 - t);
  loop invariant (myl3 - t) <= 1;
  loop invariant s == \at(s, Pre);
  loop assigns t30, ndxi, myl3, kxd;
*/
while (myl3<=t) {
      t30 = t30 + ndxi;
      ndxi = ndxi + kxd;
      myl3 += 1;
      kxd += 2;
  }
}