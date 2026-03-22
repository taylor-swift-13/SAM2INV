int main1(){
  int m3, ms8, i2, im, a, e1;
  m3=1+16;
  ms8=0;
  i2=3;
  im=0;
  a=0;
  e1=1*4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i2 - im == 3;
  loop invariant a == 0;
  loop invariant 0 <= im && im <= m3;
  loop invariant 0 <= e1 && e1 <= 4;
  loop invariant i2 == 3 + im;
  loop invariant im <= m3;
  loop invariant e1 >= 0;
  loop invariant e1 <= 4;
  loop invariant ms8 == 0;
  loop invariant e1 == (4 >> im);
  loop assigns a, e1, im, i2;
*/
while (1) {
      if (!(im<m3)) {
          break;
      }
      a = a*2;
      e1 += ms8;
      im++;
      i2 += 1;
      e1 = e1/2;
  }
}