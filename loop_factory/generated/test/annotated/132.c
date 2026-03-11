int main1(int z){
  int d, m, c54;
  d=(z%14)+20;
  m=0;
  c54=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == \at(z, Pre) % 14 + 20;
  loop invariant 0 <= m;
  loop invariant m % 5 == 0;
  loop invariant m <= d + 4;
  loop invariant (m == 0 ==> c54 == d) && (m >= 5 ==> c54 == d - m + 5);
  loop invariant 1 <= c54;
  loop invariant z == \at(z, Pre) + (m*(2*d - m + 5))/10;
  loop assigns c54, m, z;
*/
while (m<d) {
      c54 = d-m;
      m = m + 5;
      z += c54;
  }
}