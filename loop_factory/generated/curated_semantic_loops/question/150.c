int main1(int m,int q){
  int n, t, f;

  n=(q%38)+9;
  t=n;
  f=n;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (t>0) {
      f = q+5;
      t = t-1;
  }
/*@
  assert !(t>0) &&
         (n == (q % 38) + 9);
*/

}
