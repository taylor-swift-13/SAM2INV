int main1(int y){
  int aq, c00, lmha, re, l0, q;
  aq=y+16;
  c00=0;
  lmha=aq;
  re=aq;
  l0=12;
  q=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aq == \at(y, Pre) + 16;
  loop invariant y == \at(y, Pre);
  loop invariant l0 == 12;
  loop invariant c00 >= 0;
  loop invariant (l0 - c00 * y) >= 0;
  loop invariant q == -5 + c00 * (l0 % 6);
  loop invariant lmha >= aq;
  loop invariant re >= aq;
  loop invariant (aq >= 0 ==> c00 <= aq);
  loop invariant (c00 == 0) ==> (lmha == aq && re == aq && q == -5);
  loop assigns lmha, q, c00, re;
*/
while (1) {
      if (!(c00 < aq && l0 - (c00 + 1) * y >= 0)) {
          break;
      }
      lmha = lmha*2+2;
      q = q+(l0%6);
      c00 = c00 + 1;
      re = (2)+(re*lmha);
  }
}