int main1(int a,int p){
  int b, d, t;

  b=61;
  d=b;
  t=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant d % 3 == 1;
  loop invariant d >= 0;
  loop invariant b == 61;
  loop invariant d <= 61;
  loop invariant d >= 1;
  loop invariant d <= b;
  loop assigns d;
*/
while (d>2) {
      d = d-3;
  }

}
