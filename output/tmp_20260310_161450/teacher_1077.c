int main1(int k,int p){
  int n, g, v, x;

  n=38;
  g=n+3;
  v=0;
  x=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant x % 5 == 0;
  loop invariant v % 2 == 0;
  loop invariant v >= 0 && x >= 0;
  loop invariant x % 5 == 0 && x <= 5 * v && v >= 0 && v <= 2 * n;
  loop invariant k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant x >= 0 && x % 5 == 0 && v >= 0;
  loop invariant v % 2 == 0 && k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant x >= 0;
  loop invariant v >= 0;
  loop invariant v + 2 >= 2 * (x / 5 + 1);
  loop invariant x % 5 == 0 && x >= 0 && v % 2 == 0;
  loop invariant v >= 0 && k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant x <= 5 * v;
  loop invariant v <= 2 * n;
  loop invariant x % 5 == 0 && x >= 0 && v >= 0 && v % 2 == 0;
  loop assigns x, v;
*/
while (v<n) {
      x = x+5;
      v = v+1;
      v = v*2;
  }
/*@
  assert !(v<n) &&
         (k == \at(k, Pre));
*/


}
