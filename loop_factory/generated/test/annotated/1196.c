int main1(){
  int t0pt, va, mv, p, hn, r, pcp;
  t0pt=1-6;
  va=1;
  mv=va;
  p=12;
  hn=t0pt;
  r=t0pt;
  pcp=t0pt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hn*mv + r*p == -65;
  loop invariant 1 <= p;
  loop invariant pcp >= t0pt;
  loop invariant 2 <= mv + p <= 13;
  loop invariant mv >= 1;
  loop invariant hn <= 0;
  loop invariant r <= 0;
  loop assigns mv, p, r, hn, pcp;
*/
while (1) {
      if (!(mv!=p)) {
          break;
      }
      if (mv>p) {
          mv -= p;
          r += hn;
      }
      else {
          p = p - mv;
          hn += r;
      }
      pcp += p;
  }
}