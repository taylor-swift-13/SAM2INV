int main1(){
  int w8, g4, hnq, h;
  w8=1*5;
  g4=0;
  hnq=0;
  h=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h + g4 == w8;
  loop invariant hnq == g4*w8 - g4*(g4 - 1)/2;
  loop invariant g4 >= 0;
  loop invariant g4 <= w8;
  loop assigns g4, hnq, h;
*/
while (1) {
      if (!(g4<w8&&h>0)) {
          break;
      }
      g4 += 1;
      hnq += h;
      h = h - 1;
  }
}