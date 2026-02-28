int main1(int k,int m){
  int t, u, v;

  t=(m%14)+15;
  u=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u && u <= t && (u == 0 ==> v == k) && t == (m % 14) + 15;
  loop invariant k == \at(k,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant u >= 0;
  loop invariant u <= t;
  loop invariant t == (\at(m,Pre) % 14) + 15;
  loop invariant (u == 0) ==> v == \at(k,Pre);
  loop invariant u > 0 ==> v >= 0;
  loop invariant t == (m % 14) + 15;
  loop invariant 0 <= u;
  loop invariant u == 0 ==> v == \at(k, Pre);
  loop assigns v, u;
*/
while (u<t) {
      v = v*v;
      u = u+1;
  }

}
