int main1(int k,int q){
  int b, n, w, v;

  b=k;
  n=0;
  w=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (w<b) {
      if (w>=b/2) {
          v = v+2;
      }
      w = w+1;
  }
/*@
  assert !(w<b) &&
         (b == k);
*/

}
