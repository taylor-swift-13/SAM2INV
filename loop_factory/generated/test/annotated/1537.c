int main1(){
  int g0, bj, b, l, q, h8bz, k, ox, z, c;
  g0=1;
  bj=0;
  b=bj;
  l=bj;
  q=bj;
  h8bz=bj;
  k=2;
  ox=g0;
  z=g0;
  c=bj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (bj == 2*b) || (bj == 2*b + 1);
  loop invariant (bj / 5) == c;
  loop invariant z == 1 + (bj / 3);
  loop invariant 0 <= bj <= g0;
  loop invariant b == bj / 2;
  loop invariant z == 1 + bj / 3;
  loop invariant c == bj / 5;
  loop invariant ox == (1 + (bj / 2) * ((bj + 1) / 2)) % 7;
  loop invariant l == bj
                       + (3 * (bj / 3) * (bj / 3) - (bj / 3)) / 2
                       + (bj / 3) * (bj % 3);
  loop invariant k == 2
                       + (5 * (bj / 5) * (bj / 5) - 3 * (bj / 5)) / 2
                       + (bj / 5) * (bj % 5);
  loop invariant 0 <= b;
  loop invariant 0 <= z;
  loop invariant 0 <= c;
  loop invariant 2 <= k;
  loop invariant 0 <= h8bz;
  loop invariant 0 <= l;
  loop invariant 0 <= q;
  loop invariant bj <= g0;
  loop assigns bj, b, z, c, k, h8bz, ox, l, q;
*/
while (bj < g0) {
      bj = bj + 1;
      if ((bj % 2) == 0) {
          b += 1;
      }
      if ((bj % 3) == 0) {
          z += 1;
      }
      if ((bj % 5) == 0) {
          c = c + 1;
      }
      k = k + c;
      h8bz += b;
      ox = (ox+b)%7;
      l += z;
      q += h8bz;
      h8bz += l;
  }
}