int main1(int h,int s){
  int r, sy, z3, y7, gq, e;
  r=41;
  sy=r;
  z3=0;
  y7=0;
  gq=8;
  e=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == \at(s,Pre) + 3*y7;
  loop invariant s == \at(s,Pre) + sy*y7;
  loop invariant z3 == h*y7;
  loop invariant r == 41;
  loop invariant y7 >= 0;
  loop invariant y7 <= r;
  loop invariant e == s - 38 * y7;
  loop assigns z3, e, s, y7;
*/
while (y7<r) {
      z3 += h;
      e = e + 3;
      s += sy;
      y7 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gq % 2 == 0;
  loop invariant e >= \at(s, Pre) + 3;
  loop assigns r, e, gq;
*/
while (e<=z3-1) {
      r += h;
      e += 1;
      gq = gq + e;
      gq = gq*2;
  }
}