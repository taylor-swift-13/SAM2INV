int main1(int n){
  int wc7, rj, k, ybv;
  wc7=53;
  rj=wc7;
  k=rj;
  ybv=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rj >= 3;
  loop invariant ybv >= 1;
  loop invariant n - \at(n, Pre) >= ybv - 1;
  loop invariant k == 53;
  loop invariant wc7 == 53;
  loop assigns n, ybv, rj;
*/
while (rj>3) {
      ybv = ybv + k;
      n = n + ybv;
      rj = 3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n >= \at(n, Pre);
  loop invariant ybv >= 0;
  loop invariant wc7 == 53;
  loop assigns ybv;
*/
while (1) {
      if (!(ybv>=5)) {
          break;
      }
      ybv = ybv - 5;
  }
}