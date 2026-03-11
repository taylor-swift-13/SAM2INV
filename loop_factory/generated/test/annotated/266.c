int main1(){
  int li, ojw, pn, h;
  li=66;
  ojw=li;
  pn=2;
  h=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ojw <= li);
  loop invariant (2 <= pn);
  loop invariant (pn <= 8);
  loop invariant (h == 1) || (h == -1);
  loop invariant li == 66;
  loop invariant ((pn + ojw) % 2 == 0);
  loop assigns h, ojw, pn;
*/
while (ojw<li) {
      if (!(pn<8)) {
          h = -1;
      }
      if (pn<=2) {
          h = 1;
      }
      ojw = ojw + 1;
      pn += h;
  }
}