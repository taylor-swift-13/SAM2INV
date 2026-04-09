int main1(int s){
  int ng7, oy0, bkz, n;
  ng7=s*4;
  oy0=0;
  bkz=-4;
  n=ng7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n + oy0 == ng7;
  loop invariant bkz == -4;
  loop invariant ng7 == \at(s, Pre) * 4;
  loop invariant s == \at(s, Pre) + ( (ng7*(ng7-1)) - (n*(n-1)) ) / 2;
  loop invariant (ng7 > 0) ==> (oy0 >= 0 && oy0 <= ng7 && n >= 0 && n <= ng7);
  loop invariant 0 <= oy0;
  loop invariant s == \at(s, Pre) + oy0 * ng7 - (oy0 * (oy0 + 1)) / 2;
  loop assigns bkz, n, oy0, s;
*/
while (oy0 < ng7) {
      if (bkz > 0) {
          bkz--;
      }
      if (!(!(n > 0))) {
          n = n - 1;
      }
      oy0++;
      s += n;
  }
}