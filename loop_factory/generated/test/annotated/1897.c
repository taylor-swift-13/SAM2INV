int main1(int t){
  int el3f, n, ikb, an6x, it, e, g0, v6, rp1;
  el3f=47;
  n=0;
  ikb=n;
  an6x=5;
  it=n;
  e=t;
  g0=t;
  v6=0;
  rp1=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (n == it);
  loop invariant (0 <= n <= el3f);
  loop invariant (t >= \at(t, Pre));
  loop invariant (v6 >= 0);
  loop invariant ikb == n;
  loop invariant an6x == 5 + n*(n+1)/2;
  loop invariant rp1 >= 0;
  loop invariant g0 == \at(t, Pre) + n;
  loop invariant e == \at(t, Pre) + n;
  loop assigns n, rp1, it, ikb, g0, e, an6x, t, v6;
*/
while (1) {
      if (!(n < el3f)) {
          break;
      }
      n += 1;
      rp1 += 1;
      if (rp1 >= t) {
          rp1 = 0;
      }
      it += 1;
      ikb++;
      g0++;
      e += 1;
      an6x += ikb;
      if (n+4<=t+el3f) {
          t += 1;
      }
      v6 = v6 + an6x;
      v6 += 4;
  }
}