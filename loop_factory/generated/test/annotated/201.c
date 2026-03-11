int main1(){
  int hqwg, s, p1, kq, al;
  hqwg=1+24;
  s=hqwg;
  p1=-3;
  kq=0;
  al=hqwg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kq == ((p1 - 1) * p1 * (2 * p1 - 1)) / 6 + 14;
  loop invariant al == (p1 * (p1 + 1)) / 2 + 22;
  loop invariant -3 <= p1 <= hqwg + 1;
  loop assigns kq, p1, al;
*/
while (1) {
      if (!(p1<=hqwg)) {
          break;
      }
      kq = kq+p1*p1;
      p1 += 1;
      al = al + p1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kq >= 0;
  loop invariant p1 <= al;
  loop invariant hqwg >= 25;
  loop invariant (hqwg - kq*(p1 - 26)) == 25;
  loop assigns s, hqwg, p1;
*/
while (p1<al) {
      s = al-p1;
      hqwg += kq;
      p1 += 1;
  }
}