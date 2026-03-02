int main1(int p,int q){
  int y, j, d, v;

  y=p+11;
  j=0;
  d=4;
  v=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == p + 11;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant d <= 4 || d <= y + 1;
  loop invariant p == \at(p, Pre) && q == \at(q, Pre);
  loop invariant y == p + 11 && p == \at(p, Pre) && q == \at(q, Pre);
  loop invariant d >= 0 && (d <= y - 2) ==> (d % 3 == 1);

  loop invariant d % 3 == 1 || d == y+1;
  loop invariant y == \at(p, Pre) + 11;

  loop assigns d;
*/
while (1) {
      if (d+2<=y) {
          d = d+2;
      }
      else {
          d = y;
      }
      d = d+1;
  }

}
