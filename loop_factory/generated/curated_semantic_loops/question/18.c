int main1(int a,int m,int p){
  int n, e, l, c, g, t;

  n=a+9;
  e=0;
  l=m;
  c=6;
  g=-1;
  t=e;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (1) {
      if (l>=n) {
          break;
      }
      if (g<=c) {
          c = g;
      }
      l = l+1;
      l = l+5;
  }
/*@
  assert (l >= n);
*/
/*@
  assert (l - m) % 6 == 0;
*/
/*@
  assert n == a + 9;
*/

}
