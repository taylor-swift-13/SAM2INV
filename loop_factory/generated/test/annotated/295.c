int main1(){
  int y, gnic, p, j8r;
  y=1+19;
  gnic=0;
  p=0;
  j8r=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gnic >= 0;
  loop invariant p == (gnic*(gnic-1))/2;
  loop invariant j8r == p + gnic;
  loop invariant y == 20;
  loop invariant gnic <= y;
  loop invariant gnic >= 0 && gnic <= y &&
                   p == (gnic * (gnic - 1)) / 2 &&
                   j8r == (gnic * (gnic + 1)) / 2;
  loop assigns p, gnic, j8r;
*/
while (gnic<y) {
      p = p + gnic;
      gnic = gnic + 1;
      j8r = j8r + gnic;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 190;
  loop invariant j8r + 2*gnic <= 2*p;
  loop invariant 0 <= j8r;
  loop assigns gnic, j8r;
*/
while (gnic<=p-1) {
      gnic = gnic + 1;
      j8r = (p)+(-(gnic));
      j8r += j8r;
  }
}