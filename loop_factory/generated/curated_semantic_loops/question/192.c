int main1(int m,int n){
  int v, k, h, s;

  v=42;
  k=v;
  h=m;
  s=m;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (k>=3) {
      h = h+s+s;
      h = h+1;
      k = k-3;
  }
/*@
  assert !(k>=3) &&
         (k >= 0);
*/

}
