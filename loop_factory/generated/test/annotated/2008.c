int main1(){
  int mjb, yko, jty, qmb;
  mjb=1;
  yko=0;
  jty=0;
  qmb=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= yko <= mjb;
  loop invariant jty == 2 * yko;
  loop invariant qmb >= 0;
  loop invariant qmb % 2 == 0;
  loop invariant mjb == 1;
  loop assigns jty, qmb, yko;
*/
while (1) {
      if (!(yko < mjb)) {
          break;
      }
      jty += 2;
      qmb = qmb + yko;
      qmb += qmb;
      yko = yko + 1;
  }
}