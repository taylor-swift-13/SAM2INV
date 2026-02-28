int main1(int k,int m){
  int l, u, v, t;

  l=42;
  u=2;
  v=l;
  t=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == l + 2*(u - 2);
  loop invariant u <= l;
  loop invariant l == 42;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v == 2*u + 38;

  loop invariant v == 2*u + (l - 4);
  loop invariant u >= 2;
  loop invariant v - 2*u == l - 4;
  loop invariant l - u >= 0;
  loop invariant v >= l;
  loop assigns v, u;
*/
while (1) {
      if (u>=l) {
          break;
      }
      v = v+2;
      u = u+1;
  }

}
