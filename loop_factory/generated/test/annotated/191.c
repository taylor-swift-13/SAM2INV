int main1(){
  int px, c, x, mh;
  px=1;
  c=3;
  x=16;
  mh=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c >= 3;
  loop invariant mh == ((c * c + 7 * c - 24) / 2);
  loop invariant x  == ((c * c * c + 12 * c * c - 49 * c + 108) / 6);
  loop invariant px == 1;
  loop assigns x, mh, c;
*/
while (1) {
      if (!(c<px)) {
          break;
      }
      x += 2;
      mh += 4;
      mh = mh + c;
      x = x + mh;
      c = c + 1;
  }
}