int main1(){
  int r5, d9t;
  r5=26;
  d9t=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= d9t;
  loop invariant r5 == 26;
  loop invariant d9t % 2 == 0;
  loop invariant d9t <= r5 - 1;
  loop assigns d9t;
*/
while (d9t<r5) {
      if (d9t<r5/2) {
          d9t = d9t + 3;
      }
      else {
          d9t = d9t - 3;
      }
      d9t = d9t + 1;
  }
}