int main1(int w,int x){
  int trkc, af, kw, hq, vz3, lhzg, m, cx, pu;
  trkc=x*5;
  af=0;
  kw=w;
  hq=8;
  vz3=w;
  lhzg=af;
  m=w;
  cx=trkc;
  pu=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant trkc == 5 * \at(x, Pre);
  loop invariant af >= 0;
  loop invariant hq >= 8;
  loop invariant kw + hq == \at(w, Pre) + 8 + af;
  loop invariant cx == (trkc + hq - 8);
  loop invariant vz3 == (\at(w, Pre) + 5 * af);
  loop invariant (af <= trkc) || (\at(x,Pre) < 0);
  loop invariant lhzg == af * \at(w,Pre) + 5 * (af * (af + 1) / 2);
  loop invariant 2 * (cx - trkc) == af - (af % 2);
  loop invariant x >= \at(x, Pre);
  loop assigns kw, af, hq, cx, w, pu, x, vz3, lhzg, m;
*/
while (1) {
      if (!(af < trkc)) {
          break;
      }
      if (!(!((af % 2) == 0))) {
          kw++;
          af++;
      }
      else {
          hq++;
          cx = cx + 1;
          af++;
      }
      if ((af%7)==0) {
          w = hq+kw;
      }
      pu = pu + cx;
      x = x + hq;
      vz3 = vz3 + 1;
      vz3 += 4;
      lhzg = lhzg + vz3;
      m = m + lhzg;
  }
}