int main1(int b,int w){
  int r6ij, ryl, sa7, j6hv, tl;
  r6ij=b-9;
  ryl=0;
  sa7=0;
  j6hv=1;
  tl=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (sa7 == 0) || (j6hv == sa7 - 3);
  loop invariant ryl == 0;
  loop invariant tl == b;
  loop invariant sa7 >= 0;
  loop invariant tl == \at(b, Pre);
  loop invariant (sa7 == 0 ==> j6hv == 1) && (sa7 != 0 ==> j6hv + 3 == sa7);
  loop invariant sa7 % 4 == 0;
  loop invariant r6ij == b - 9;
  loop assigns j6hv, sa7, tl;
*/
while (sa7+4<=r6ij+4-1) {
      j6hv = sa7+1;
      sa7 += 4;
      tl = tl + ryl;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ryl == 0) || (ryl == sa7 + 3);
  loop invariant r6ij == \at(b,Pre) - 9;
  loop invariant b >= \at(b, Pre);
  loop assigns b, j6hv, ryl;
*/
while (1) {
      if (!(sa7+4<=ryl)) {
          break;
      }
      j6hv = j6hv+r6ij*sa7;
      b = b + sa7;
      ryl = (sa7+4)-1;
  }
}