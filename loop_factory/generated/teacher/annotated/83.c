int main1(int a,int m){
  int l, u, v;

  l=m+18;
  u=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant l == m + 18;

  loop invariant v >= 0;
  loop invariant v >= 2*u;
  loop invariant u >= 0;
  loop invariant v >= 2*u - 2;
  loop invariant v % 2 == 0;
  loop invariant (u <= l) || (l < 0);
  loop invariant l == \at(m, Pre) + 18;

  loop assigns u, v;
*/
while (u<l) {
      v = v+1;
      v = v+v;
      u = u+1;
  }

}
