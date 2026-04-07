int main1(int a){
  int epx, ojg, uil, lsr8, r2g;
  epx=38;
  ojg=0;
  uil=3;
  lsr8=epx;
  r2g=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r2g == ojg;
  loop invariant uil == 3 + ((ojg * (ojg + 1)) / 2);
  loop invariant lsr8 % epx == 0;
  loop invariant lsr8 >= epx;
  loop invariant (0 <= ojg && ojg <= epx);
  loop invariant 2*(uil - 3) == (ojg * (ojg + 1));
  loop assigns ojg, lsr8, r2g, uil;
*/
while (1) {
      if (!(ojg < epx)) {
          break;
      }
      ojg += 1;
      lsr8 = lsr8 + lsr8;
      r2g = r2g + 1;
      uil += ojg;
  }
}