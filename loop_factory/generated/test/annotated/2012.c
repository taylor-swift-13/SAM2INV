int main1(int w){
  int cm7, au8, c, dw, v;
  cm7=w;
  au8=0;
  c=au8;
  dw=11;
  v=au8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == (au8 * (au8 - 3));
  loop invariant v == (2 * au8);
  loop invariant dw == (11 + 2 * au8);
  loop invariant au8 >= 0;
  loop invariant (cm7 >= 0) ==> (au8 <= cm7);
  loop invariant cm7 == \at(w, Pre);
  loop assigns au8, c, dw, v;
*/
while (au8 < cm7) {
      au8 = (c--, dw--, v--, au8 + 1);
      dw = dw + 3;
      c += v;
      v = v + 3;
  }
}