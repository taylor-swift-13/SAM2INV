int main1(int b,int n){
  int m, j, l, v;

  m=(n%37)+7;
  j=0;
  l=b;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(n, Pre);
  loop invariant m == \at(n, Pre) % 37 + 7;
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);

  loop invariant (3 + 2*v == 0) ==> l == \at(b, Pre);

  loop invariant 3 + 2*v != 0;

  loop invariant (2*v + 3 == 0) ==> l == \at(b, Pre);

  loop invariant v == \at(n, Pre) && m == (\at(n, Pre) % 37 + 7) && b == \at(b, Pre);

  loop assigns l;
*/
while (1) {
      l = l+3;
      l = l+v+v;
  }

}
