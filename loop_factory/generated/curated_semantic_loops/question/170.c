int main1(int k,int p){
  int r, c, v;

  r=k-5;
  c=0;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (c<=r-1) {
      v = v+v;
      if (v+7<r) {
          v = v%8;
      }
      c = c+1;
  }
/*@
  assert !(c<=r-1) &&
         (r == k - 5);
*/

}
