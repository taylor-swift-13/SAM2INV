int main1(){
  int p, zp3g, fg8e;
  p=1+25;
  zp3g=2;
  fg8e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 26;
  loop invariant fg8e <= p;
  loop invariant 0 <= fg8e;
  loop invariant zp3g == 2 + fg8e;
  loop assigns zp3g, fg8e;
*/
while (1) {
      if (!(fg8e<=p-1)) {
          break;
      }
      zp3g++;
      fg8e += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == fg8e;
  loop invariant p <= zp3g;
  loop assigns p, fg8e;
*/
while (p<zp3g) {
      p++;
      fg8e += 1;
  }
}