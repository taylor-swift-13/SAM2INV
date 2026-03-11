int main1(int m,int n){
  int a, g, v;

  a=n;
  g=0;
  v=5;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (g<a) {
      v = v+v;
      v = v+g;
      g = g+1;
  }
/*@
  assert !(g<a) &&
         (a == n && m == \at(m, Pre) && n == \at(n, Pre));
*/

}
