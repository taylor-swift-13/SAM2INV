int main1(int m,int n){
  int t, tonb, tz, hi;
  t=n;
  tonb=0;
  tz=0;
  hi=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= tz;
  loop invariant (m - \at(m, Pre)) == tz;
  loop invariant m - hi == \at(m,Pre);
  loop invariant (n - \at(n,Pre)) % 3 == 0 && ((tonb == 0) || (tonb == t));
  loop invariant t == \at(n, Pre);
  loop invariant (tonb == 0) ==> (tz == 0);
  loop invariant (tonb == 0) ==> (n == \at(n, Pre));
  loop invariant n == \at(n, Pre) || n == \at(n, Pre) + 3;
  loop assigns hi, m, n, tz, tonb;
*/
while (1) {
      if (!(tonb<t)) {
          break;
      }
      if (tz+4<=t) {
          tz += 4;
      }
      else {
          tz = t;
      }
      n = n + 3;
      hi += tz;
      m += tz;
      tonb = t;
  }
}