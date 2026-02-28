int main1(int n){
  int r, q, z, s;

  r=(n%11)+17;
  q=r;
  z=8;
  s=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre);
  loop invariant r == (\at(n, Pre) % 11) + 17;
  loop invariant 0 <= q;
  loop invariant q <= (\at(n, Pre) % 11) + 17;
  loop invariant r == (\at(n, Pre) % 11 + 17);
  loop invariant q <= r;
  loop invariant q >= 0;
  loop invariant q <= \at(n,Pre) % 11 + 17;
  loop invariant r == \at(n,Pre) % 11 + 17;
  loop assigns q;
*/
while (q-1>=0) {
      q = q-1;
  }

}
