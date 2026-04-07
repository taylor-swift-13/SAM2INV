int main1(){
  int a3, hh3, k, ug, w, l, sl, hl2;
  a3=1+20;
  hh3=0;
  k=hh3;
  ug=1*2;
  w=hh3;
  l=a3;
  sl=a3;
  hl2=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant -1 <= hl2 && hl2 < 4;
  loop invariant 0 <= w && w < 7;
  loop invariant 0 <= ug && ug < 8;
  loop invariant 0 <= k && k < 9;
  loop invariant 0 <= hh3 && hh3 <= a3;
  loop invariant k == ((hh3 * (hh3 + 1)) / 2) % 9;
  loop invariant sl >= a3;
  loop invariant a3 <= sl;
  loop invariant 0 <= hh3 <= a3;
  loop invariant 0 <= k <= 8;
  loop invariant 0 <= ug <= 7;
  loop invariant 0 <= w <= 6;
  loop invariant 0 <= l <= a3;
  loop invariant -1 <= hl2 <= 3;
  loop invariant sl >= 0;
  loop invariant -a3 <= l <= a3;
  loop invariant 0 <= sl;
  loop invariant k == (((hh3 * (hh3 + 1)) / 2) % 9);
  loop invariant 0 <= hh3;
  loop invariant hh3 <= a3;
  loop assigns hh3, k, ug, w, l, hl2, sl;
*/
while (1) {
      if (!(hh3 < a3)) {
          break;
      }
      hh3++;
      k = (k + hh3) % 9;
      ug = (ug + k) % 8;
      w = (w + ug) % 7;
      l = (l + w) % 6;
      hl2 = (hl2 + l) % 4;
      if (k<a3+5) {
          sl = sl + sl;
      }
      if (sl<a3+4) {
          sl = sl + hh3;
      }
      if (!(!(sl+4<a3))) {
          sl = l%10;
      }
  }
}