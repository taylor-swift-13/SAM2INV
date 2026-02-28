int main1(int a,int n){
  int l, v, b;

  l=(n%36)+4;
  v=2;
  b=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant l == ((\at(n, Pre) % 36) + 4);
  loop invariant v >= 2;
  loop invariant l == ((\at(n,Pre)) % 36) + 4;
  loop invariant (v == 2) ==> (b == a);

  loop invariant l == (\at(n, Pre) % 36) + 4;
  loop invariant v >= 2 && (b <= a || b <= 1);
  loop invariant l == (n % 36) + 4;
  loop assigns b, v;
*/
while (1) {
      b = b-b;
      if ((v%6)==0) {
          b = b+1;
      }
      v = v+1;
  }

}
