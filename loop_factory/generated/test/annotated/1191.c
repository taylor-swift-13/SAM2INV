int main1(){
  int mbyu, es, jr, d, so, bq, r8v;
  mbyu=(1%20)+13;
  es=mbyu+6;
  jr=-2;
  d=es;
  so=0;
  bq=mbyu;
  r8v=mbyu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (jr % 2 == 0);
  loop invariant (d % 2 == 0);
  loop invariant ((d - jr) % 2) == 0;
  loop invariant mbyu == 14;
  loop invariant d >= 20;
  loop invariant jr <= 0;
  loop invariant so >= 0;
  loop invariant r8v >= 0;
  loop invariant bq >= mbyu;
  loop invariant bq >= 14;
  loop assigns jr, d, so, bq, r8v;
*/
while (1) {
      if (!(jr!=d)) {
          break;
      }
      if (jr>d) {
          jr -= d;
          bq += so;
      }
      else {
          d -= jr;
          so = so + bq;
      }
      r8v = r8v+bq-bq;
      r8v = r8v*r8v;
  }
}