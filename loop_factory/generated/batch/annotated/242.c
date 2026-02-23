int main1(int m,int n){
  int l, v, o;

  l=n+9;
  v=l;
  o=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == n + 9;
  loop invariant v <= l;

  loop invariant v % 4 == l % 4;
  loop invariant (l >= 6) ==> o >= 0;
  loop invariant l == \at(n, Pre) + 9 &&
                   n == \at(n, Pre) &&
                   m == \at(m, Pre) &&
                   l - v >= 0 &&
                   (l - v) % 4 == 0;

  loop invariant l == \at(n, Pre) + 9;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (v - l) % 4 == 0;

  loop invariant v <= \at(n, Pre) + 9;
  loop invariant (v - (\at(n, Pre) + 9)) % 4 == 0;
  loop invariant (\at(n, Pre) + 9 == 0) <==> (o == 0);
  loop assigns o, v;
*/
while (v>3) {
      o = o*2;
      if (v+6<=v+l) {
          o = o*o;
      }
      v = v-4;
  }

}
