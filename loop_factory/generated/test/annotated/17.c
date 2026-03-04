int main1(int i){
  int b, w7, e;
  b=(i%37)+12;
  w7=b;
  e=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == (\at(i,Pre) % 37) + 12;
  loop invariant e - 3*w7 == -3*b - 5;
  loop invariant e == -5 + 3*(w7 - b);
  loop invariant w7 <= b;
  loop invariant e >= -5;
  loop invariant w7 >= b;
  loop assigns e, w7, i;
*/
while (1) {
      if (!(w7<b)) {
          break;
      }
      e = e + 3;
      w7 = w7 + 1;
      i += w7;
      if (w7+6<=e+b) {
          i = i - i;
      }
  }
}