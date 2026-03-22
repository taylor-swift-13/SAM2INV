int main1(int r){
  int dw5u, cn, y0z, hs, r3, j3;
  dw5u=r;
  cn=-3;
  y0z=0;
  hs=0;
  r3=r;
  j3=dw5u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r3 <= dw5u + 1;
  loop invariant dw5u == r;
  loop invariant j3 == r;
  loop invariant y0z == 0;
  loop invariant cn == -3;
  loop invariant dw5u == \at(r, Pre);
  loop invariant r <= r3;
  loop invariant hs == 4 * (r3 - r);
  loop assigns cn, y0z, r3, hs, j3;
*/
while (1) {
      if (r3>dw5u) {
          break;
      }
      cn = cn + y0z;
      y0z = (hs)+(y0z);
      r3 = r3 + 1;
      hs += 4;
      j3 = j3+(hs%4);
  }
}