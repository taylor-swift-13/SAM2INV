int main1(int r){
  int hn, xbkk, xm, bq;
  hn=(r%8)+20;
  xbkk=hn;
  xm=hn;
  bq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xbkk <= ((\at(r, Pre) % 8) + 20);
  loop invariant xbkk >= 0;
  loop invariant xbkk % 3 == (((\at(r, Pre) % 8) + 20) % 3);
  loop invariant hn == (r % 8) + 20;
  loop invariant r == \at(r, Pre);
  loop assigns xbkk;
*/
while (xbkk>2) {
      xbkk = xbkk - 3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xbkk <= ((\at(r, Pre) % 8) + 20);
  loop invariant hn >= ((\at(r, Pre) % 8) + 20);
  loop invariant bq == 0;
  loop invariant xbkk >= 0;
  loop invariant xm > 0;
  loop invariant r <= \at(r, Pre);
  loop assigns xbkk, xm, hn, r;
*/
while (xbkk>hn) {
      xbkk -= hn;
      xm = xm + bq;
      hn++;
      r = r/3;
      xm = xm*3;
  }
}