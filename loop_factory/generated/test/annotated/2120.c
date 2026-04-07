int main1(int o){
  int jqh, w5, ri, lm, c73f;
  jqh=(o%9)+16;
  w5=0;
  ri=o;
  lm=o;
  c73f=w5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= w5;
  loop invariant w5 <= jqh;
  loop invariant ri == o + w5;
  loop invariant lm == o + w5;
  loop invariant c73f == w5 * o + w5 * (w5 + 1) / 2;
  loop invariant jqh == (\at(o, Pre) % 9) + 16;
  loop invariant ri == (\at(o, Pre) + w5);
  loop invariant lm == (\at(o, Pre) + w5);
  loop invariant c73f == (w5 * \at(o, Pre) + (w5 * (w5 + 1)) / 2);
  loop invariant jqh == (o % 9) + 16;
  loop assigns lm, w5, ri, c73f;
*/
while (w5 < jqh) {
      lm++;
      w5++;
      ri = ri + 1;
      c73f = c73f + ri;
  }
}