int main1(int n,int q){
  int u, f, l, v;

  u=n;
  f=0;
  l=f;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == n;
  loop invariant f >= 0;
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v * q >= 0;

  loop invariant (q == 0) ==> (v == 0);
  loop invariant u == \at(n, Pre);
  loop invariant (f == 0) ==> (v == q);
  loop invariant q == \at(q, Pre) && n == \at(n, Pre);
  loop invariant u == n && f >= 0;
  loop invariant f >= 0 && u == n && q == \at(q, Pre) && n == \at(n, Pre);
  loop assigns v, f;
*/
while (1) {
      v = v+v;
      f = f+1;
  }

}
