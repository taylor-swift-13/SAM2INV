int main1(int k,int m){
  int f, x, v, q;

  f=33;
  x=0;
  v=0;
  q=0;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v<f) {
      if (v<f/2) {
          q = q+2;
      }
      else {
          q = q-2;
      }
      v = v+1;
  }
/*@
  assert !(v<f) &&
         ((v <= f));
*/

}
