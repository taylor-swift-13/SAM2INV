int main1(int d,int p){
  int s4, ca2, z;
  s4=d+11;
  ca2=s4;
  z=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == -4 + 3*(ca2 - s4);
  loop invariant p == \at(p, Pre);
  loop invariant ca2 <= s4;
  loop invariant ca2 >= \at(d, Pre) + 11;
  loop invariant d == \at(d, Pre) + (ca2 - s4)*(2*p - 1) + (3 * (ca2 - s4) * ((ca2 - s4) - 1)) / 2;
  loop invariant d == \at(d, Pre) - 4*(ca2 - s4) + (3*(ca2 - s4)*((ca2 - s4) + 1))/2 + 2*p*(ca2 - s4);
  loop invariant ca2 >= s4;
  loop assigns ca2, z, d;
*/
while (ca2<s4) {
      z = z + 3;
      ca2 = ca2 + 1;
      d += z;
      d = d+p+p;
  }
}