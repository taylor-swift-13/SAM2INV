int main1(int x,int g){
  int hr, c1q, xq, k9, xj;
  hr=36;
  c1q=hr;
  xq=-1;
  k9=c1q;
  xj=c1q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (c1q % 3) == 0;
  loop invariant 0 <= c1q <= 36;
  loop invariant g == \at(g, Pre);
  loop invariant x == \at(x, Pre);
  loop assigns c1q;
*/
for (; c1q-3>=0; c1q = c1q - 3) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hr >= 36;
  loop invariant xj >= 0;
  loop invariant k9 + hr <= 72;
  loop invariant (xj % 2) == 0;
  loop invariant c1q >= 0;
  loop invariant g <= \at(g, Pre);
  loop invariant x == \at(x, Pre);
  loop invariant k9 > 0;
  loop invariant g == \at(g, Pre) + (hr - 36) * xq;
  loop assigns k9, hr, xj, c1q, g;
*/
while (1) {
      if (!(k9>hr)) {
          break;
      }
      k9 -= hr;
      hr += 1;
      xj = xj*2;
      c1q = ((hr%2))+(c1q);
      g = g + xq;
  }
}