int main1(){
  int n6, rh, u, ml5, d;
  n6=1;
  rh=n6;
  u=n6;
  ml5=n6;
  d=n6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n6 == 1;
  loop invariant rh >= 0;
  loop invariant rh <= n6;
  loop invariant d + n6 * rh == 1 + n6;
  loop invariant u == n6;
  loop invariant ml5 == n6;
  loop assigns rh, d;
*/
for (; rh>0&&u>0&&ml5>0; rh = rh - 1) {
      d += n6;
  }
}