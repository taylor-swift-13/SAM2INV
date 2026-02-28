int main1(int b,int n){
  int o, f, c, v;

  o=67;
  f=3;
  c=n;
  v=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant c == n + 2*(f - 3);
  loop invariant f <= o;
  loop invariant f >= 3;
  loop invariant c - 2*f == n - 6;
  loop invariant c - \at(n, Pre) == 2*(f - 3);
  loop invariant o == 67;
  loop invariant n == \at(n, Pre);
  loop invariant c - n == 2*(f - 3);
  loop invariant c <= n + 2*(o - 3);
  loop invariant c == \at(n,Pre) + 2*(f - 3);
  loop assigns c, f;
*/
while (1) {
      if (f>=o) {
          break;
      }
      c = c+2;
      f = f+1;
  }

}
