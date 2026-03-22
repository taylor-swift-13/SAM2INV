int main1(){
  int jz, g6, l7, kj, y;
  jz=58;
  g6=0;
  l7=jz;
  kj=jz;
  y=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 0;
  loop invariant kj == 58;
  loop invariant (l7 % jz) == 0;
  loop invariant 0 <= g6;
  loop invariant g6 < jz;
  loop invariant jz == 58;
  loop assigns g6, kj, l7;
*/
while (1) {
      if (!(g6 < jz)) {
          break;
      }
      kj = kj + y;
      l7 = l7 + l7;
      g6 = (g6 + 1) % jz;
  }
}