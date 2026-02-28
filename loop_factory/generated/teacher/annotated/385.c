int main1(int a,int q){
  int c, t, d;

  c=36;
  t=0;
  d=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 0;
  loop invariant c == 36;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant d >= 36;
  loop invariant d % 5 == 1;
  loop invariant t <= c;
  loop invariant (d - 36) % 5 == 0;
  loop invariant d >= c;
  loop invariant (d - c) % 5 == 0;
  loop invariant t >= 0;
  loop assigns d;
*/
while (t<c) {
      d = d+4;
      if ((t%4)==0) {
          d = d+1;
      }
  }

}
