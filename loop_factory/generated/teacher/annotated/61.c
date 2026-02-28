int main1(int k,int m){
  int t, u, v;

  t=(m%14)+15;
  u=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u && u <= t;
  loop invariant t == (m % 14) + 15;
  loop invariant v >= 2*u;
  loop invariant 0 <= u;
  loop invariant u <= t;
  loop invariant v >= u + 2;
  loop invariant v % 2 == 0;
  loop invariant v + 2 == (1 << (u + 2));
  loop invariant m == \at(m, Pre) && k == \at(k, Pre);
  loop invariant v >= 2*u + 2;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop assigns v, u;
*/
while (u<t) {
      v = v+1;
      v = v+v;
      u = u+1;
  }

}
