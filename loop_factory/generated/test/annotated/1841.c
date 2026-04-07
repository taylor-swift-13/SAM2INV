int main1(int w){
  int f4g, e, kn3, t, xbto;
  f4g=w+18;
  e=0;
  kn3=0;
  t=0;
  xbto=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == xbto;
  loop invariant kn3 == e * w;
  loop invariant t == e * w;
  loop invariant 0 <= e;
  loop assigns e, kn3, t, xbto;
*/
while (e < f4g) {
      kn3 = kn3 + w;
      e += 1;
      xbto = xbto + w;
      t = t + w;
  }
}