int main1(int m,int n){
  int r, u, v, p;

  r=53;
  u=0;
  v=0;
  p=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == p*(m + 1);
  loop invariant 0 <= p && p <= r;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == p * (m + 1);
  loop invariant v == p*(m + 1) && 0 <= p && p <= r;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant v == p*(m+1);
  loop invariant 0 <= p && p <= r && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant v == p*(m+1) && 0 <= p && p <= r;
  loop invariant v == p*(\at(m, Pre) + 1);
  loop invariant 0 <= p <= r;
  loop invariant p >= 0 && p <= r && m == \at(m, Pre) && n == \at(n, Pre);
  loop assigns v, p;
*/
while (p<r) {
      v = v+m;
      p = p+1;
      v = v+1;
  }

}
