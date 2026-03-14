int main1(){
  int o, azl3, fqp0, jr, m5m;
  o=(1%30)+4;
  azl3=o;
  fqp0=-4;
  jr=0;
  m5m=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 16*m5m == fqp0*fqp0 + 2*fqp0 - 104;
  loop invariant o == 5;
  loop invariant -6 <= m5m <= o - 1;
  loop assigns fqp0, m5m, jr;
*/
while (1) {
      if (!(fqp0<o)) {
          break;
      }
      jr = fqp0+5;
      m5m += jr;
      fqp0 += 8;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o < fqp0;
  loop invariant o >= 5;
  loop invariant azl3 >= 5;
  loop assigns azl3, o;
*/
while (1) {
      azl3 += azl3;
      o = o + 1;
      if (o>=fqp0) {
          break;
      }
  }
}