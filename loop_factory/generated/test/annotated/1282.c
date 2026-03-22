int main1(){
  int pw, vt, m4, c9, rfi, xs;
  pw=1*5;
  vt=1;
  m4=0;
  c9=0;
  rfi=0;
  xs=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 5 <= xs <= 5 + 4*(vt - 1);
  loop invariant c9 == (vt - 1) % 5;
  loop invariant 1 <= vt;
  loop invariant vt <= pw;
  loop invariant m4 >= 0;
  loop invariant xs - vt >= 4;
  loop invariant xs - 5 == m4;
  loop invariant 0 <= rfi < 5;
  loop assigns c9, m4, rfi, vt, xs;
*/
while (vt<pw) {
      c9 = vt%5;
      if (!(!(vt>=xs))) {
          rfi = (vt-xs)%5;
          m4 = m4+c9-rfi;
      }
      else {
          m4 += c9;
      }
      vt = vt + 1;
      xs += c9;
  }
}