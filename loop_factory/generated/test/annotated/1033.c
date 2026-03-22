int main1(int g){
  int px, ufr, y, seq, s9x;
  px=g*4;
  ufr=0;
  y=1;
  seq=0;
  s9x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant seq == (y - 1) * (y - 1);
  loop invariant s9x == (y - 1) * px;
  loop invariant y >= 1;
  loop assigns seq, y, s9x;
*/
while (1) {
      if (!(y<=px)) {
          break;
      }
      seq = seq+2*y-1;
      y++;
      s9x = s9x+px-ufr;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y >= 1;
  loop invariant seq >= 0;
  loop invariant (s9x <= px - 1) ==> (seq >= 1);
  loop assigns s9x, seq, y;
*/
while (s9x<=px-1) {
      s9x++;
      seq = (px)+(-(s9x));
      y = y + seq;
  }
}