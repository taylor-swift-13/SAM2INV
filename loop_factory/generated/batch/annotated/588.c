int main1(int a,int q){
  int l, k, u, v;

  l=q-8;
  k=0;
  u=8;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == q - 8;
  loop invariant v == l;
  loop invariant u == 8 + 2*v*k;

  loop invariant k >= 0;
  loop invariant (l <= 0) ==> (k == 0);
  loop invariant u == 8 + 2*l*k;
  loop invariant 0 <= k;
  loop invariant (l < 0) || (k <= l);
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns u, k;
*/
while (k<l) {
      u = u+v+v;
      k = k+1;
  }

}
