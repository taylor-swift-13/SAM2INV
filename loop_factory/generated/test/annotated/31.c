int main1(int a){
  int bj, r, y;
  bj=a+12;
  r=0;
  y=bj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= r;
  loop invariant a == \at(a,Pre) + r*(\at(a,Pre) + 12) - r*(r+1)/2;
  loop invariant y == \at(a,Pre) + 12 + 3*r;
  loop invariant y == bj + 3*r;
  loop invariant bj == \at(a, Pre) + 12;
  loop invariant a == \at(a, Pre) + r*bj - r*(r+1)/2;
  loop invariant (bj > 0) ==> (r <= bj);
  loop invariant r >= 0;
  loop assigns a, r, y;
*/
while (1) {
      if (!(r<bj)) {
          break;
      }
      y = y + 3;
      r = r + 1;
      a = a+bj-r;
  }
}