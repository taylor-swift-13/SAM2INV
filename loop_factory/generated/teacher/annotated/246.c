int main1(int a,int m){
  int o, d, v, u;

  o=m+25;
  d=1;
  v=a;
  u=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == m + 25;
  loop invariant m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant d >= 1;
  loop invariant d < o ==> o - d > 0;
  loop invariant o == \at(m, Pre) + 25;
  loop invariant d == 1 || d % 2 == 0;
  loop invariant d > 0;

  loop assigns d;
*/
while (d<o) {
      d = d*2;
  }

}
