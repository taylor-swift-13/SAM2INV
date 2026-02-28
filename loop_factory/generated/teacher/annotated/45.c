int main1(int a,int q){
  int m, d, v, o, y, h;

  m=a-10;
  d=0;
  v=-1;
  o=-8;
  y=-8;
  h=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == d - 1;
  loop invariant (d == 0 ==> h == \at(q, Pre)) && (d > 0 ==> h == d - 2 + o + y);
  loop invariant o == -8 && y == -8;
  loop invariant m == \at(a, Pre) - 10;
  loop invariant a == \at(a, Pre) && q == \at(q, Pre);
  loop invariant (d == 0) ==> h == \at(q, Pre);
  loop invariant d >= 1 ==> h == d - 2 + o + y;
  loop invariant d <= m || d == 0;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant o == -8;
  loop invariant y == -8;
  loop invariant 0 <= d;
  loop invariant m == a - 10;
  loop invariant (d == 0) ==> (h == q);

  loop invariant (d >= 1) ==> (h == v - 17);
  loop assigns d, v, h;
*/
while (d<m) {
      h = v+o+y;
      v = v+1;
      d = d+1;
  }

}
