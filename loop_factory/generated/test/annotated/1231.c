int main1(int y){
  int uh4, d3e, d7se, l, a9, d;
  uh4=(y%11)+19;
  d3e=0;
  d7se=d3e;
  l=3;
  a9=-1;
  d=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == \at(y, Pre) + d*(d+1)/2;
  loop invariant a9 == -1 + 2*d;
  loop invariant l == d*d - 2*d + 3;
  loop invariant d7se == d*(2*d*d - 9*d + 25) / 6;
  loop invariant 0 <= d <= uh4 + 1;
  loop invariant d >= 0;
  loop invariant y - d*(d+1)/2 == \at(y, Pre);
  loop invariant 6*d7se == d*(2*d*d - 9*d + 25);
  loop invariant 0 <= d;
  loop invariant d7se == (2*d*d*d - 9*d*d + 25*d)/6;
  loop assigns d, d7se, l, a9, y;
*/
while (1) {
      if (d>uh4) {
          break;
      }
      d7se += l;
      l += a9;
      a9 += 2;
      d++;
      y += d;
  }
}