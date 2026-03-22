int main1(){
  int y4, c, wmn, vcug, qe, f7, f, e6b, h8, wxdq;
  y4=(1%38)+12;
  c=0;
  wmn=0;
  vcug=0;
  qe=0;
  f7=0;
  f=0;
  e6b=0;
  h8=0;
  wxdq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == c;
  loop invariant wxdq == c;
  loop invariant wmn == c / 4;
  loop invariant vcug == (c + 3) / 4;
  loop invariant qe == (c + 2) / 4;
  loop invariant f7 == (c + 1) / 4;
  loop invariant e6b == c * (c + 9) / 2;
  loop invariant (c == 0) ==> (h8 == 0);
  loop invariant 0 <= c <= y4;
  loop invariant h8 >= 0;
  loop assigns c, wmn, vcug, qe, f7, f, h8, e6b, wxdq;
*/
while (1) {
      if (!(c < y4)) {
          break;
      }
      c = c + 1;
      if ((c % 4) == 0) {
          wmn += 1;
      }
      if (!(!((c % 4) == 1))) {
          vcug += 1;
      }
      if ((c % 4) == 2) {
          qe++;
      }
      if ((c % 4) == 3) {
          f7++;
      }
      f = f + 1;
      h8 = h8 + vcug;
      e6b += f;
      e6b += 4;
      wxdq += 1;
  }
}