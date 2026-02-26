int main1(int b,int n){
  int y, e, q;

  y=9;
  e=0;
  q=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant e % 5 == 0;
  loop invariant q == \at(n, Pre) + e/5;
  loop invariant (0 <= e);
  loop invariant (e <= y);
  loop invariant y == 9;
  loop invariant 0 <= e;
  loop invariant e <= y;
  loop invariant q >= \at(n, Pre);
  loop invariant q == \at(n, Pre) + (5*(e/5)*(e/5) - 3*(e/5)) / 2;
  loop invariant q == n + (e/5) + (5 * (((e/5) - 1) * (e/5))) / 2;
  loop invariant e == 0 || e == 5;
  loop invariant q - n <= 1;
  loop invariant q >= n;
  loop invariant q == n + (e*e - 3*e)/10;
  loop assigns q, e;
*/
while (e<=y-5) {
      q = q+e;
      q = q+1;
      e = e+5;
  }

}
