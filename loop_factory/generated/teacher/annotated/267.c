int main1(int k,int m){
  int t, u, v;

  t=(m%14)+15;
  u=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant u == 0;
  loop invariant u <= t;
  loop invariant t == (\at(m, Pre) % 14) + 15;
  loop invariant (v - \at(k, Pre)) % 2 == 0;
  loop invariant v >= \at(k, Pre);

  loop invariant v >= k;
  loop invariant (v - k) % 2 == 0;

  loop invariant 0 <= u;
  loop assigns v;
*/
while (u<t) {
      v = v+2;
      v = v+u;
  }

}
