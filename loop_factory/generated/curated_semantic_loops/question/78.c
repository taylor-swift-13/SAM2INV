int main1(int k,int m){
  int t, u, v;

  t=(m%14)+15;
  u=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (u<t) {
      v = v*v;
      u = u+1;
  }
/*@
  assert !(u<t) &&
         (0 <= u && u <= t && (u == 0 ==> v == k) && t == (m % 14) + 15);
*/

}
