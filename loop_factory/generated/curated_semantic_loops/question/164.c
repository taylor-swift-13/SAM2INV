int main1(int b,int k){
  int m, t, i;

  m=b+3;
  t=0;
  i=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (t<m) {
      i = i+i;
      if ((t%9)==0) {
          i = i+2;
      }
      t = t+1;
  }
/*@
  assert !(t<m) &&
         (m == b + 3);
*/

}
