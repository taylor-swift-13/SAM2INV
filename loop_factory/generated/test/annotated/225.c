int main1(){
  int se5, h4d, khd, nh, vo, f;
  se5=1+8;
  h4d=se5;
  khd=5;
  nh=0;
  vo=se5;
  f=h4d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= nh;
  loop invariant nh <= se5;
  loop invariant khd == 5 + nh;
  loop invariant f == h4d * (nh + 1);
  loop invariant h4d == se5;
  loop invariant vo >= se5;
  loop invariant vo <= se5 + 8 * nh;
  loop invariant ((vo - se5 - (nh * 5 + (nh * (nh + 1)) / 2)) % 9) == 0;
  loop assigns khd, nh, f, vo;
*/
while (nh<=se5-1) {
      khd += 1;
      nh++;
      f += h4d;
      vo = vo+(khd%9);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vo >= se5;
  loop invariant h4d == se5;
  loop invariant f >= h4d;
  loop invariant h4d > 0;
  loop invariant f % h4d == 0;
  loop assigns f, vo;
*/
while (se5*2<=vo) {
      f += h4d;
      vo = (se5*2)-1;
  }
}