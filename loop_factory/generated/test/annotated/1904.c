int main1(int n){
  int eeok, b3, dmly, u, ek, ooy, pb, vy7, o;
  eeok=127;
  b3=0;
  dmly=b3;
  u=b3;
  ek=n;
  ooy=0;
  pb=1;
  vy7=0;
  o=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= b3;
  loop invariant b3 <= eeok;
  loop invariant dmly == b3 / 2;
  loop invariant pb == 1 + (b3/2) * ((b3+1)/2);
  loop invariant ooy == b3;
  loop invariant vy7 == 3 * b3;
  loop invariant u == (b3 + 1) / 2;
  loop invariant ek == \at(n, Pre) + (b3 / 2);
  loop invariant n - 3*b3 == \at(n,Pre);
  loop assigns b3, dmly, u, ek, n, o, ooy, pb, vy7;
*/
while (b3 < eeok) {
      b3 += 1;
      if ((b3 % 2) == 0) {
          dmly = dmly + 1;
      }
      if (!(!((b3 % 2) != 0))) {
          u = u + 1;
      }
      else {
          ek++;
      }
      o = o + u;
      n = n + 3;
      ooy++;
      pb += dmly;
      vy7 = vy7 + 3;
  }
}