int main1(int b,int m){
  int n, u, o, v;

  n=60;
  u=0;
  o=m;
  v=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= u) && (u <= n);
  loop invariant o == m + u;
  loop invariant v == 8 - u;
  loop invariant u <= n;
  loop invariant 0 <= u;
  loop invariant u >= 0;
  loop invariant m == \at(m, Pre);
  loop invariant o == \at(m, Pre) + u;
  loop invariant v + u == 8;
  loop assigns o, u, v;
*/
while (u<n) {
      o = o+1;
      v = v-1;
      u = u+1;
  }

}
