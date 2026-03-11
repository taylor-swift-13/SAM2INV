int main1(int k,int m){
  int t, u, v;

  t=(m%14)+15;
  u=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (u<t) {
      v = v+1;
      v = v+v;
      u = u+1;
  }
/*@
  assert !(u<t) &&
         (0 <= u && u <= t);
*/

}
