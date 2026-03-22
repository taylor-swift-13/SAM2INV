int main1(int n){
  int o, eg, k, be, r;
  o=(n%7)+17;
  eg=2;
  k=o;
  be=eg;
  r=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == (\at(n,Pre) % 7) + 17;
  loop invariant n == \at(n,Pre) + eg * (k - o);
  loop invariant eg == 2;
  loop invariant o <= k <= o + 1;
  loop invariant r >= 1;
  loop invariant be >= 2;
  loop assigns be, r, k, n;
*/
while (k<=o) {
      be = be*k;
      if (k<o) {
          r = r*k;
      }
      k += 1;
      n += eg;
  }
}