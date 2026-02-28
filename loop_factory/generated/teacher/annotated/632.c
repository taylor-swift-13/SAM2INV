int main1(int n,int q){
  int o, p, v, l, a, w;

  o=n-6;
  p=0;
  v=6;
  l=p;
  a=-2;
  w=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 6 + 3*p;
  loop invariant o == n - 6;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant p >= 0;
  loop invariant p > 0 ==> w == v + l + a;
  loop invariant p == 0 ==> w == 1;
  loop invariant l == 0;
  loop invariant (p > 0) ==> (w == v + l + a);
  loop invariant (p == 0) ==> (w == 1);
  loop invariant o == \at(n, Pre) - 6;
  loop invariant a == -2;
  loop assigns v, p, w;
*/
while (1) {
      if (p>=o) {
          break;
      }
      v = v+3;
      p = p+1;
      w = v+l+a;
  }

}
