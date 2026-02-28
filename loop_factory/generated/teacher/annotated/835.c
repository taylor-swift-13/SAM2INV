int main1(int k,int n,int q){
  int c, o, v, u, p, h;

  c=(q%33)+13;
  o=0;
  v=o;
  u=n;
  p=k;
  h=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == o;
  loop invariant u + v == n;
  loop invariant o >= 0;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant o == v;
  loop invariant u == n - v;
  loop invariant h == q;
  loop invariant c == \at(q, Pre) % 33 + 13;
  loop invariant c == (\at(q,Pre) % 33) + 13;
  loop invariant u + o == n;
  loop invariant v >= 0;
  loop invariant c == (q % 33) + 13;

  loop invariant (v + c - n - 6) < 0  ==> p == k + v*(v-1)/2;
  loop assigns v, u, p, o;
*/
while (1) {
      v = v+1;
      u = u-1;
      p = p+o;
      if (u+6<c) {
          p = p+h;
      }
      o = o+1;
  }

}
