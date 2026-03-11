int main1(int t){
  int a, ph, y9q, itp, v;
  a=(t%25)+8;
  ph=0;
  y9q=1;
  itp=5;
  v=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant itp == 5 + (y9q - 1) * y9q * (2 * y9q - 1) / 6;
  loop invariant v == -4;
  loop invariant ph == 0;
  loop invariant t == \at(t, Pre);
  loop assigns itp, v, y9q;
*/
while (y9q<=a) {
      itp = itp+y9q*y9q;
      v += ph;
      y9q = y9q + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -4;
  loop invariant t - v*a == \at(t, Pre) - (-4) * (((\at(t, Pre)) % 25) + 8);
  loop assigns y9q, t, a;
*/
while (a<itp) {
      y9q = itp-a;
      t += v;
      a++;
  }
/*@
  assert !(a<itp) &&
         (itp == 5 + (y9q - 1) * y9q * (2 * y9q - 1) / 6);
*/

}