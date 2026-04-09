int main1(){
  int it, z2, ro, d, p;
  it=(1%25)+11;
  z2=0;
  ro=z2;
  d=6;
  p=it;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= z2;
  loop invariant z2 <= it;
  loop invariant p == it + 2*z2;
  loop invariant d == 6 - z2;
  loop invariant ro == z2*(it + 9) + (z2*(z2 - 1))/2;
  loop assigns z2, p, d, ro;
*/
while (z2 < it) {
      z2 = (p = p + 1, d = d - 1, z2 + 1);
      ro += 2;
      p++;
      ro = ro+d+p;
  }
}