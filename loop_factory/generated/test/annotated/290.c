int main1(int l,int k){
  int c, t, mb, fe1;
  c=68;
  t=0;
  mb=0;
  fe1=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t <= c;
  loop invariant 0 <= mb;
  loop invariant mb <= 6;
  loop invariant l - \at(l, Pre) == mb;
  loop invariant fe1 == 1 || fe1 == -1;
  loop invariant 0 <= t;
  loop invariant k == \at(k, Pre);
  loop invariant -t <= l - \at(l, Pre);
  loop invariant l - \at(l, Pre) <= t;
  loop invariant \at(l, Pre) - t <= l;
  loop assigns l, mb, t, fe1;
*/
while (t<c) {
      if (mb>=6) {
          fe1 = -1;
      }
      if (mb<=0) {
          fe1 = 1;
      }
      mb += fe1;
      t += 1;
      l += fe1;
  }
}