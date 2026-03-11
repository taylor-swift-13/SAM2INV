int main1(){
  int j, wt9n, yl3, b, z, a0u;
  j=25;
  wt9n=0;
  yl3=0;
  b=0;
  z=j;
  a0u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= b);
  loop invariant (b <= j);
  loop invariant (yl3 == b);
  loop invariant (z == j + b * wt9n);
  loop assigns yl3, b, z, a0u;
*/
while (b<j) {
      yl3++;
      b += 1;
      z += wt9n;
      a0u = a0u+(yl3%9);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wt9n == 0;
  loop invariant z == j;
  loop invariant yl3 == j;
  loop invariant a0u >= 0;
  loop assigns z, yl3, a0u;
*/
while (1) {
      if (!(z<=wt9n-1)) {
          break;
      }
      z += 1;
      yl3 += wt9n;
      a0u++;
  }
/*@
  assert b == j;
*/
/*@
  assert yl3 == j;
*/
/*@
  assert wt9n == 0 && z == j && yl3 == j;
*/

}
