int main1(){
  int wa, n, wgv, o9, u0w;
  wa=1+20;
  n=wa;
  wgv=-3;
  o9=0;
  u0w=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o9 == wgv + 3;
  loop invariant u0w <= 9;
  loop invariant o9 == 285 - (u0w * (u0w + 1) * (2 * u0w + 1)) / 6;
  loop invariant n >= 0;
  loop invariant wgv >= -3;
  loop assigns o9, n, wgv, u0w;
*/
while (1) {
      if (!(u0w>0)) {
          break;
      }
      o9 = o9+u0w*u0w;
      n = n+wgv*wgv;
      wgv = wgv+u0w*u0w;
      u0w = u0w - 1;
      n = n*n+n;
  }
}