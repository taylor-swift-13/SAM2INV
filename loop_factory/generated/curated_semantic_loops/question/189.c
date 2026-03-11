int main1(int a,int q){
  int n, h, f;

  n=25;
  h=0;
  f=n;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (h<n) {
      f = q%3;
      f = f+6;
      h = h+3;
  }
/*@
  assert !(h<n) &&
         (h >= 0);
*/

}
