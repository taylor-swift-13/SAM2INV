int main1(){
  int n, ew;
  n=1-7;
  ew=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == 1 - 7;
  loop invariant ew <= n;
  loop assigns ew;
*/
while (ew<=n) {
      ew += ew;
  }
}