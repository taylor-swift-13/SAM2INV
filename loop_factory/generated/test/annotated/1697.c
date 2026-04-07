int main1(){
  int o0, k5l, fc, yx;
  o0=1;
  k5l=0;
  fc=1*4;
  yx=o0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k5l <= o0;
  loop invariant yx == 1;
  loop invariant fc == 4 + 3 * k5l;
  loop invariant o0 == 1;
  loop invariant k5l >= 0;
  loop assigns fc, k5l;
*/
while (1) {
      if (!(k5l < o0)) {
          break;
      }
      fc = fc + yx;
      k5l++;
      fc = fc+yx+yx;
  }
}