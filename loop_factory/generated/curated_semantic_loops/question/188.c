int main1(int b,int k){
  int a, s, c, n;

  a=80;
  s=0;
  c=-17823;
  n=2;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (c<=-3) {
      c = c+n-1;
      n = n+2;
  }
/*@
  assert !(c<=-3) &&
         (4*(c + 17823) == (n - 2)*(n - 2));
*/

}
