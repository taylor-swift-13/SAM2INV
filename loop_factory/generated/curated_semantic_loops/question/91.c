int main1(int k,int m){
  int l, r, i;

  l=10;
  r=l;
  i=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (r>=1) {
      if ((r%9)==0) {
          i = i+i;
      }
      r = r-1;
  }
/*@
  assert !(r>=1) &&
         (l == 10);
*/

}
