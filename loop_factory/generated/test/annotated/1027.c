int main1(){
  int a, u9k, ni, v9, u, x;
  a=1*2;
  u9k=a;
  ni=0;
  v9=u9k;
  u=u9k;
  x=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= ni && ni <= a);
  loop invariant u == u9k * (ni + 1);
  loop invariant a == 2;
  loop invariant u9k == a;
  loop invariant (ni == 0) ==> (v9 == a);
  loop invariant (ni > 0) ==> (v9 == a - (ni - 1));
  loop assigns v9, ni, u;
*/
while (ni<a) {
      v9 = a-ni;
      ni += 1;
      u = u + u9k;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x >= 2;
  loop invariant a == 2;
  loop invariant u9k == a;
  loop invariant (u9k - x) >= 0;
  loop assigns x;
*/
while (1) {
      if (!(x<=u9k-1)) {
          break;
      }
      x = x + 1;
  }
}