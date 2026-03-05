int main1(){
  int b, g, iq;
  b=(1%6)+4;
  g=0;
  iq=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 5;
  loop invariant 0 <= iq;
  loop invariant iq <= 2*b + 5;
  loop invariant g >= 0;
  loop invariant g <= b - 1;
  loop assigns g, iq;
*/
while (1) {
      if (iq+3<=b) {
          iq = iq + 3;
      }
      else {
          iq = b;
      }
      iq += iq;
      iq = iq + 5;
      g++;
      if (g>=b) {
          break;
      }
  }
}