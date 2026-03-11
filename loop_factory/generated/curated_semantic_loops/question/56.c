int main1(int p){
  int l, k, r, b;

  l=p+7;
  k=l;
  r=l;
  b=l;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (r<l) {
      if (r<l) {
          r = r+1;
      }
      r = r+2;
  }
/*@
  assert !(r<l) &&
         (l == p + 7);
*/

}
