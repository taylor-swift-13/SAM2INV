int main1(int a,int n){
  int b, o, v, j;

  b=n;
  o=1;
  v=b;
  j=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == n;
  loop invariant o >= 1;
  loop invariant v >= b;
  loop invariant o == 1 ==> v == b;
  loop invariant o >= 1 && (o == 1 ==> v == b);
  loop invariant (o >= 2) ==> (v % 2 == 0);
  loop invariant (o == 1) ==> (v == \at(n, Pre));
  loop invariant a == \at(a, Pre) && b == n;
  loop invariant o <= b && v >= b && o >= 1 && (o > 1) ==> (v % 2 == 0);
  loop invariant o <= b || b <= 1;
  loop invariant (n >= 1) ==> (o <= n) && (v >= n);

  loop invariant n == \at(n,Pre) && a == \at(a,Pre) && b == \at(n,Pre);
  loop invariant b == n && v >= b && o >= 1;
  loop invariant a == \at(a, Pre) && n == \at(n, Pre) && b == n && o >= 1;
  loop assigns v, o;
*/
while (1) {
      if (o>=b) {
          break;
      }
      v = v+1;
      o = o+1;
      v = v*2;
  }

}
