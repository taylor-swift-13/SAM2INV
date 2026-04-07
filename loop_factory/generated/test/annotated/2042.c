int main1(){
  int r, f92, kyww, xy, i, wx;
  r=1;
  f92=0;
  kyww=r;
  xy=r;
  i=2;
  wx=f92;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 1;
  loop invariant kyww == xy;
  loop invariant wx == 0;
  loop invariant 0 <= f92;
  loop invariant f92 <= r;
  loop invariant (f92 == 0) ==> (i == 2);
  loop invariant kyww + wx == r;
  loop assigns f92, i, kyww, wx;
*/
while (1) {
      if (!(f92 < r)) {
          break;
      }
      f92 += 1;
      i = kyww - xy;
      kyww = kyww + (xy - kyww)/r;
      wx = wx + i/r;
  }
}