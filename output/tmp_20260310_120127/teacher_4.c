int main1(int a,int k){
  int r, u, v, y, d, f;

  r=a;
  u=0;
  v=8;
  y=u;
  d=-3;
  f=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(a, Pre);
  loop invariant u >= 0;
  loop invariant r == a;
  loop invariant u == 0 || u <= r;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v == u + 8;
  loop invariant 0 <= u;

  loop assigns u, v;
*/
while (u<r) {
      v = v+1;
      u = u+1;
  }

}
