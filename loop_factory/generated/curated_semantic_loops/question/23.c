int main1(){
  int se5, h4d, khd, nh, vo, f;
  se5=1+8;
  h4d=se5;
  khd=5;
  nh=0;
  vo=se5;
  f=h4d;
  /* >>> LOOP INVARIANT TO FILL <<< */

while (nh<=se5-1) {
      khd += 1;
      nh++;
      f += h4d;
      vo = vo+(khd%9);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */

while (se5*2<=vo) {
      f += h4d;
      vo = (se5*2)-1;
  }
/*@
  assert !(se5*2<=vo) &&
         (0 <= nh);
*/

}