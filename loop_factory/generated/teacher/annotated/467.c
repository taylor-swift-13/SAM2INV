int main1(int a,int m){
  int o, d, v, u;

  o=m+25;
  d=0;
  v=o;
  u=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == o + 2*d;
  loop invariant u == a + d*o + d*(d+1);
  loop invariant d >= 0;
  loop invariant o == m + 25;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant u == a + d*d + d*(o+1);
  loop invariant u == a + d*(m + 26) + d*d;
  loop invariant u == a + d*(m+25) + d*(d+1);
  loop assigns v, u, d;
*/
while (1) {
      v = v+2;
      u = u+v;
      d = d+1;
  }

}
