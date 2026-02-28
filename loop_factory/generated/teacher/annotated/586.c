int main1(int n,int q){
  int u, f, l, v;

  u=n;
  f=0;
  l=f;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 0;
  loop invariant f >= 0;
  loop invariant n == \at(n,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant u == n;
  loop invariant (f == 0) ==> (v == q);
  loop invariant (f > 0) ==> (v % 2 == 0);
  loop invariant (q > 0) ==> (v > 0);
  loop invariant (q == 0) ==> (v == 0);
  loop assigns v, f;
*/
while (1) {
      v = v+v;
      v = v+l;
      f = f+1;
  }

}
