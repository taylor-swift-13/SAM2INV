int main1(int n,int q){
  int k, i, t, v;

  k=q+13;
  i=0;
  t=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == v * (n + 4);

  loop invariant k == \at(q, Pre) + 13;
  loop invariant k == q + 13;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant 0 <= v;
  loop invariant v >= 0;
  loop invariant (k >= 0) ==> v <= k;

  loop invariant t == (n + 4) * v;
  loop invariant t == v*(n + 4);
  loop assigns t, v;
*/
while (v<k) {
      t = t+n;
      v = v+1;
      t = t+4;
  }

}
