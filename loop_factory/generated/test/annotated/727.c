int main1(){
  int w5, x8, v42;
  w5=0;
  x8=(1%28)+10;
  v42=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x8 == 11 - (w5*(w5 - 1))/2;
  loop invariant w5 >= 0;
  loop invariant 0 <= v42 - 4 <= 7 * w5;
  loop invariant v42 >= 4;
  loop assigns v42, w5, x8;
*/
while (1) {
      if (!(x8>w5)) {
          break;
      }
      x8 -= w5;
      w5++;
      v42 = v42+(x8%8);
  }
}