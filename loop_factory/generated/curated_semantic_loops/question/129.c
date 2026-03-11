int main1(int a,int n){
  int w, u, v, q;

  w=n;
  u=w;
  v=u;
  q=a;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v<w) {
      if (v<w) {
          v = v+1;
      }
      v = v+1;
  }
/*@
  assert !(v<w) &&
         (w == n);
*/

}
