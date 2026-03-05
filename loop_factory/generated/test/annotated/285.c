int main1(){
  int x7w, ghr, ptu, bk0;
  x7w=26;
  ghr=0;
  ptu=0;
  bk0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ghr <= x7w;
  loop invariant bk0 == ghr % 7;
  loop invariant ptu == ghr + ghr/7;
  loop invariant 0 <= bk0;
  loop invariant bk0 <= 6;
  loop assigns ghr, ptu, bk0;
*/
for (; ghr<x7w; ghr = ghr + 1) {
      ptu = ptu + 1;
      bk0++;
      if (bk0>=7) {
          bk0 = bk0 - 7;
          ptu = ptu + 1;
      }
  }
}