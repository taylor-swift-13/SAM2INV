int main1(int z){
  int l4, gh, t, h9, n4, wuz;
  l4=54;
  gh=0;
  t=0;
  h9=(z%28)+10;
  n4=5;
  wuz=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gh == 0;
  loop invariant l4 == 54;
  loop invariant t >= 0;
  loop invariant n4 > 0;
  loop invariant wuz == -3 + t * (l4 - gh);
  loop invariant h9 == ((\at(z, Pre) % 28) + 10) - t*(t - 1)/2;
  loop invariant z == \at(z, Pre) + t * gh;
  loop assigns h9, wuz, z, n4, t;
*/
while (h9>t) {
      h9 -= t;
      wuz = wuz+l4-gh;
      z = z + gh;
      n4 = n4*n4+n4;
      t += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gh >= 0;
  loop invariant l4 == 54;
  loop invariant n4 >= 0;
  loop invariant wuz >= -3;
  loop assigns h9, gh, n4, wuz, z;
*/
while (n4>0) {
      h9 = h9+z*z;
      gh = gh+z*z;
      n4 = (n4)+(-(1));
      wuz = wuz+z*z;
      z += wuz;
  }
}