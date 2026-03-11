int main1(int m){
  int l, r, j;

  l=47;
  r=l;
  j=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (r-4>=0) {
      r = r-4;
  }
/*@
  assert !(r-4>=0) &&
         (l == 47);
*/

}
