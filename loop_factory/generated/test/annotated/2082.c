int main1(){
  int d2cm, aa, dh, frn;
  d2cm=1+13;
  aa=0;
  dh=1;
  frn=d2cm;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (frn + (aa * aa) == d2cm);
  loop invariant (dh == (1 + 2 * aa));
  loop invariant (0 <= aa && aa <= d2cm);
  loop invariant (frn >= 0);
  loop assigns aa, frn, dh;
*/
while (1) {
      if (!(aa < d2cm && dh <= frn)) {
          break;
      }
      aa += 1;
      frn -= dh;
      dh += 2;
  }
}