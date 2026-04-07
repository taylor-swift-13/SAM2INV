int main1(){
  int d, atb, n, pnb, v;
  d=(1%6)+18;
  atb=0;
  n=0;
  pnb=0;
  v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= atb;
  loop invariant atb <= d;
  loop invariant 0 <= n;
  loop invariant n <= d;
  loop invariant 0 <= pnb;
  loop invariant pnb <= 2 * d;
  loop invariant ((atb == 0 && n == 0 && pnb == 0 && v == 0)
                    || (atb == d && 1 <= n && n <= d && pnb == 2 * n && v == n));
  loop invariant v == n;
  loop assigns atb, pnb, n, v;
*/
while (atb < d) {
      v = (n = (pnb = (atb = atb + 1)));
      pnb += pnb;
      atb = d;
  }
}