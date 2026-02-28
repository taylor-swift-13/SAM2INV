int main1(int a,int b,int n,int q){
  int y, u, l, h, v, s, o;

  y=36;
  u=y;
  l=0;
  h=n;
  v=2;
  s=y;
  o=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 0;
  loop invariant h == n;
  loop invariant v == 2;
  loop invariant u >= 0;
  loop invariant u <= 36;
  loop invariant y == 36;
  loop invariant 0 <= u;
  loop invariant u <= y;
  loop invariant (u == 36) ==> (s == 36);
  loop invariant (u != 36) ==> (s == n + 2);
  loop assigns s, u;
*/
while (u>0) {
      s = l+h+v;
      u = u-1;
  }

}
