int main1(int b,int n){
  int y, e, q;

  y=9;
  e=0;
  q=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant y == 9;
  loop invariant ((e == 0) || (e == 5));
  loop invariant ((q == n) || (q == 2*n) || (q == 4*n));
  loop invariant (e % 5 == 0) && (0 <= e) && (e <= 5) && ((e == 0) ==> (q == n)) && ((e == 5) ==> (q == 2 * n));
  loop invariant (q == n) || (q == 2 * n);
  loop invariant e % 5 == 0 && 0 <= e && e <= y;
  loop invariant n == \at(n, Pre) && b == \at(b, Pre)
                   && ((e == 0 && q == \at(n, Pre)) || (e >= 5 && q == 2 * \at(n, Pre)));
  loop invariant e % 5 == 0;
  loop invariant e >= 0 && e <= y;
  loop invariant \at(n, Pre) != 0 ==> q % \at(n, Pre) == 0;
  loop invariant e <= y;

  loop invariant e % 5 == 0 && q == \at(n, Pre) * (e/5 + 1) && e <= y;
  loop invariant 0 <= e && b == \at(b, Pre) && n == \at(n, Pre);
  loop invariant n == \at(n, Pre) && b == \at(b, Pre);
  loop invariant 0 <= e && e <= y;
  loop invariant (e == 0) ==> q == \at(n, Pre);
  loop invariant (e == 0 && q == n) || (e == 5 && q == 2 * n);
  loop invariant (e == 0) ==> (q == \at(n, Pre));
  loop invariant (e == 0) || (e == 5);
  loop assigns q, e;
*/
while (e<=y-5) {
      q = q+q;
      e = e+5;
  }

}
