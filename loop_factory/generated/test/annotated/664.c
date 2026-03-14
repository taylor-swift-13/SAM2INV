int main1(){
  int v6, y, lt, fvsz, kip2, w4;
  v6=1;
  y=v6;
  lt=1;
  fvsz=0;
  kip2=y;
  w4=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lt == 1 + fvsz;
  loop invariant fvsz <= v6;
  loop invariant v6 == 1;
  loop invariant w4 == 1;
  loop invariant kip2 == 1 + fvsz*(v6 + w4);
  loop assigns fvsz, kip2, lt;
*/
while (fvsz<v6) {
      kip2 += v6;
      lt += 1;
      fvsz++;
      kip2 = kip2 + w4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w4 <= v6;
  loop invariant v6 == 1;
  loop invariant y == 1;
  loop invariant kip2 == fvsz + 2;
  loop invariant fvsz == w4;
  loop assigns w4, kip2, fvsz;
*/
while (w4<v6) {
      w4 = w4 + 1;
      kip2 += 1;
      fvsz = fvsz + y;
  }
}