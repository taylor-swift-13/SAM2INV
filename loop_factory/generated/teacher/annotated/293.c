int main1(int m,int p){
  int l, u, v, j;

  l=54;
  u=l+2;
  v=u;
  j=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 54;
  loop invariant u == l + 2;
  loop invariant v >= l + 2;
  loop invariant u >= l;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (v - j == 3) || (j == m && v == 56);
  loop invariant v >= 56;
  loop invariant v >= u;
  loop invariant (v - u) % 3 == 0;
  loop assigns j, v;
*/
while (u>l) {
      j = v;
      v = v+3;
  }

}
