int main1(){
  int a850, lo, k9k, vpku, w, xz;
  a850=191;
  lo=1;
  k9k=2;
  vpku=w - xz;
  w=a850;
  xz=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (lo == 1) || (lo == a850);
  loop invariant xz == -6;
  loop invariant w >= 0;
  loop invariant a850 == 191;
  loop invariant (lo == 1 && k9k == 2 && w == a850)
                   || (lo == a850 && k9k == 2 + vpku && w == a850/2);
  loop assigns vpku, k9k, w, lo;
*/
while (1) {
      if (!(lo < a850)) {
          break;
      }
      vpku = vpku + w - xz;
      k9k += vpku;
      w = w/2;
      lo = a850;
  }
}