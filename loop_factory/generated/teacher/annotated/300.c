int main1(int a,int n){
  int c, i, d, v;

  c=67;
  i=c;
  d=c;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant c == 67;
  loop invariant v <= d;
  loop invariant d >= 0;
  loop invariant d >= 67;
  loop invariant v >= 67;
  loop invariant d <= c;
  loop invariant d == v*v + v - 4489;
  loop invariant d >= v;
  loop assigns d, v;
*/
while (d<c) {
      if (d<c) {
          d = d+1;
      }
      d = d+v+v;
      d = d+1;
      v = v+1;
  }

}
