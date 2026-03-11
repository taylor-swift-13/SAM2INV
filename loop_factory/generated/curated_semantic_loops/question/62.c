int main1(int b,int k){
  int y, j, n, q, v;

  y=40;
  j=0;
  n=j;
  q=4;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (j<=y-5) {
      n = n+1;
      q = q-1;
      n = v-n;
      j = j+5;
  }
/*@
  assert !(j<=y-5) &&
         (j % 5 == 0);
*/

}
