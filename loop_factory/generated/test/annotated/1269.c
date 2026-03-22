int main1(int t){
  int lhsu, h, l1t, uim, mw;
  lhsu=t-4;
  h=0;
  l1t=t;
  uim=h;
  mw=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == \at(t, Pre);
  loop invariant uim == 0;
  loop invariant mw == 1;
  loop invariant lhsu == \at(t, Pre) - 4;
  loop invariant l1t >= \at(t, Pre);
  loop assigns uim, mw, t, l1t;
*/
while (1) {
      if (!(l1t<=lhsu)) {
          break;
      }
      uim = uim*l1t;
      if (l1t<lhsu) {
          mw = mw*l1t;
      }
      t = t + uim;
      l1t = l1t + 1;
  }
}