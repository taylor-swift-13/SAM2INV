int main1(int b,int q){
  int vb, c4, iody, z0, unf, r, j0;
  vb=b+15;
  c4=vb+7;
  iody=0;
  z0=(b%28)+10;
  unf=0;
  r=b;
  j0=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iody >= 0;
  loop invariant z0 == ((b % 28) + 10) - iody*(iody - 1)/2;
  loop invariant j0 == 4 + iody * c4;
  loop invariant unf == 0;
  loop invariant r == \at(b, Pre);
  loop invariant r == b;
  loop invariant vb == b + 15;
  loop invariant c4 == b + 22;
  loop assigns z0, unf, j0, iody, r;
*/
while (z0>iody) {
      z0 = z0 - iody;
      unf = unf*2;
      j0 = (c4)+(j0);
      iody += 1;
      r = r + unf;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant unf == 0;
  loop invariant vb <= \at(b, Pre) + 15;
  loop invariant vb <= b + 15;
  loop invariant ((\at(b,Pre) + 15) - vb) % 2 == 0;
  loop invariant q == \at(q, Pre);
  loop assigns vb;
*/
while (vb>=unf+1) {
      vb -= 2;
  }
}