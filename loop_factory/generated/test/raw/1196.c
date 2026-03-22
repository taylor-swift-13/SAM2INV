int main1(){
  int t0pt, va, mv, p, hn, r, pcp;

  t0pt=1-6;
  va=1;
  mv=va;
  p=12;
  hn=t0pt;
  r=t0pt;
  pcp=t0pt;

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
