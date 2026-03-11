int main1(int m,int n){
  int s, w, v, l;

  s=64;
  w=0;
  v=0;
  l=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= v && v <= s && s == 64 && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant (v <= s/2) ==> l == \at(n, Pre) && (v >= s/2) ==> l == \at(n, Pre) + 2*(v - s/2);
  loop invariant 0 <= v && v <= s;
  loop invariant n == \at(n, Pre) && m == \at(m, Pre);
  loop invariant ((v <= s/2) ==> l == \at(n, Pre)) && ((v >= s/2) ==> l == \at(n, Pre) + 2*(v - s/2));
  loop invariant s == 64;
  loop invariant v >= 0;
  loop invariant v <= s;
  loop invariant n == \at(n, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v <= s/2 ==> l == n;
  loop invariant v >= s/2 ==> l == n + 2*(v - s/2);
  loop invariant v < s/2 ==> l == \at(n, Pre);
  loop invariant v >= s/2 ==> l == \at(n, Pre) + 2*(v - s/2);
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant 0 <= v && v <= s && s == 64 && m == \at(m, Pre);
  loop invariant (v <= s/2 ==> l == n) && (v >= s/2 ==> l == n + 2*(v - s/2)) && n == \at(n, Pre);
  loop invariant 0 <= v && v <= s && n == \at(n, Pre) && m == \at(m, Pre) && s == 64;
  loop invariant v <= s/2 ==> l == \at(n, Pre);
  loop invariant s == 64 && 0 <= v && v <= s && m == \at(m, Pre) && n == \at(n, Pre);
  loop assigns l, v;
*/
while (v<s) {
      if (v>=s/2) {
          l = l+2;
      }
      v = v+1;
  }
/*@
  assert !(v<s) &&
         (0 <= v && v <= s && s == 64 && m == \at(m, Pre) && n == \at(n, Pre));
*/


}
