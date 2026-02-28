int main1(int b,int n){
  int m, t, d;

  m=n;
  t=0;
  d=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 0;
  loop invariant d >= n;
  loop invariant ((d - n) % 2) == 0;
  loop invariant m == n;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (d - n) % (2 + t) == 0;
  loop invariant (d - n) % 2 == 0;
  loop assigns d;
*/
while (1) {
      d = d+2;
      d = d+t;
  }

}
