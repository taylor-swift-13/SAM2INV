int main1(int n,int q){
  int b, d, v, z, p;

  b=54;
  d=0;
  v=-4;
  z=0;
  p=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -4 + 3*d && n == \at(n, Pre);
  loop invariant d <= b;
  loop invariant p == 4 + 2 * d;
  loop invariant v == -4 + 3 * d;
  loop invariant 0 <= d;
  loop invariant b == 54;
  loop invariant n == \at(n, Pre) && q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns d, v, p;
*/
while (d<b) {
      v = v+3;
      p = p+2;
      d = d+1;
  }

}
