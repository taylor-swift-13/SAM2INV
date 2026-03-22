int main1(){
  int r66w, t38o, yl8, a, zi;
  r66w=116;
  t38o=r66w;
  yl8=t38o;
  a=2;
  zi=t38o;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= t38o <= 116;
  loop invariant r66w == 116;
  loop assigns t38o;
*/
for (; t38o-1>=0; t38o -= 1) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a >= 2;
  loop invariant r66w >= 116;
  loop invariant yl8 == 116;
  loop invariant zi == r66w*r66w - 2*r66w - 13108;
  loop assigns zi, a, r66w;
*/
while (1) {
      if (!(r66w<=yl8)) {
          break;
      }
      zi = zi+2*r66w-1;
      a = a + zi;
      r66w += 1;
      a = a+t38o+t38o;
  }
}