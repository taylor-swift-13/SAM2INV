int main1(int m,int n){
  int d, i, a;

  d=(m%24)+12;
  i=0;
  a=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant d == \at(m, Pre) % 24 + 12;
  loop invariant a >= \at(m, Pre);
  loop invariant a >= m;
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant d == (\at(m,Pre) % 24) + 12;
  loop invariant d == (\at(m, Pre) % 24) + 12;
  loop invariant (a+3)*(a+4) == a*a + 7*a + 12;
  loop invariant a >= \at(m,Pre);
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant d == (\at(m, Pre) % 24 + 12);
  loop invariant a*a + 7*a + 12 >= 0;

  loop assigns a;
*/
while (1) {
      a = a+3;
      a = a*a+a;
  }

}
