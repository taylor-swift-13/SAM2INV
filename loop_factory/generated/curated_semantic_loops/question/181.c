int main1(int b,int k){
  int m, l, v, d;

  m=56;
  l=0;
  v=0;
  d=0;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v<m) {
      d = d+5;
      v = v+1;
      v = v*3+2;
  }
/*@
  assert !(v<m) &&
         (m == 56);
*/

}
