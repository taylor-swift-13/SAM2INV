int main1(int a,int n){
  int m, v, w, x;

  m=(a%11)+14;
  v=m;
  w=-2;
  x=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= m;
  loop invariant 0 <= v;
  loop invariant m == (a % 11) + 14;
  loop invariant m == ((\at(a, Pre)) % 11) + 14;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v >= 0;
  loop invariant w <= -2;
  loop invariant w % 2 == 0;
  loop invariant v <= (\at(a, Pre) % 11) + 14 &&
                   w <= -2 &&
                   w % 2 == 0;
  loop invariant a == \at(a, Pre) &&
                   n == \at(n, Pre) &&
                   m == (\at(a, Pre) % 11) + 14;
  loop assigns w, v;
*/
while (v>=1) {
      w = w*4;
      v = v-1;
  }

}
