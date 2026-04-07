int main1(int b){
  int kw, me, jvc, z5g;
  kw=(b%16)+15;
  me=0;
  jvc=0;
  z5g=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jvc == me;
  loop invariant z5g == 5;
  loop invariant kw == (\at(b, Pre) % 16 + 15);
  loop invariant 0 <= me;
  loop invariant me <= kw;
  loop assigns me, jvc, z5g;
*/
while (me < kw) {
      me = me + 1;
      jvc = me;
      z5g = z5g+jvc-jvc;
  }
}