int main1(){
  int dq, eq, y, hb, m;
  dq=1+14;
  eq=dq+1;
  y=5;
  hb=0;
  m=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dq == 1 + 14;
  loop invariant 0 <= hb;
  loop invariant hb <= dq;
  loop invariant y == 5 + hb;
  loop invariant m == ((hb * (hb + 1)) / 2) + hb * eq;
  loop invariant eq == 16;
  loop assigns y, hb, m;
*/
while (hb<dq) {
      y++;
      hb++;
      m += hb;
      m += eq;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dq == 1 + 14;
  loop invariant hb >= 1;
  loop invariant m >= 17;
  loop invariant (y >= 5);
  loop invariant eq == 16 || eq == 4*y - 1;
  loop invariant hb >= 0;
  loop assigns m, hb, eq;
*/
while (y*4<=eq) {
      m += hb;
      hb += eq;
      hb = hb*2+3;
      eq = (y*4)-1;
  }
}