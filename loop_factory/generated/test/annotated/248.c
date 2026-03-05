int main1(int n){
  int nr, d;
  nr=45;
  d=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nr == 45;
  loop invariant 0 <= d;
  loop invariant d <= nr;
  loop invariant d % 2 == 0;
  loop invariant n >= \at(n, Pre);
  loop assigns d, n;
*/
while (d<nr) {
      if (d<nr/2) {
          d++;
      }
      else {
          d -= 1;
      }
      d++;
      n += d;
  }
}