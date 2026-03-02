int main1(int m,int n){
  int h, e, c;

  h=n-5;
  e=2;
  c=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant h == \at(n, Pre) - 5;
  loop invariant c == \at(m, Pre) || c % 2 == 0;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant h == \at(n,Pre) - 5;
  loop invariant n == \at(n, Pre) && m == \at(m, Pre);
  loop invariant h == \at(n, Pre) - 5 && n == \at(n, Pre) && m == \at(m, Pre);
  loop assigns c;
*/
while (1) {
      c = c+3;
      if (c+5<h) {
          c = c+c;
      }
      c = c+c;
  }

}
