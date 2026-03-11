int main1(int a,int b){
  int z, m, o, q;

  z=49;
  m=0;
  o=z;
  q=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == z + 2*q*m && m <= z;
  loop invariant m >= 0 && a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant o == z + 2*q*m;
  loop invariant 0 <= m && m <= z;
  loop invariant q == 4;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m <= z;
  loop invariant m >= 0;
  loop invariant o == z + 2*q*m && 0 <= m && m <= z;
  loop invariant a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant 0 <= m && m <= z && a == \at(a, Pre) && b == \at(b, Pre) && q == 4;
  loop invariant q == 4 && a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant o == z + m*(q+q) && q == 4;
  loop invariant 0 <= m && m <= z && a == \at(a, Pre) && b == \at(b, Pre);
  loop assigns m, o;
*/
while (m<=z-1) {
      o = o+q+q;
      m = m+1;
  }
/*@
  assert !(m<=z-1) &&
         (o == z + 2*q*m && m <= z);
*/


}
