int main1(int b){
  int pf, ul, fu, s, qd, hp;
  pf=b-8;
  ul=pf;
  fu=0;
  s=0;
  qd=0;
  hp=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ul <= pf;
  loop invariant hp >= 7;
  loop invariant 0 <= s;
  loop invariant s <= 4;
  loop invariant 0 <= qd;
  loop invariant qd <= 4;
  loop invariant fu <= 4*(pf - ul);
  loop invariant pf == b - 8;
  loop invariant hp - 7 <= 4*(ul - pf);
  loop assigns s, fu, ul, hp, qd;
*/
while (ul<pf) {
      s = ul%5;
      if (!(!(ul>=hp))) {
          qd = (ul-hp)%5;
          fu = fu+s-qd;
      }
      else {
          fu = fu + s;
      }
      ul = ul + 1;
      hp = hp + s;
  }
}