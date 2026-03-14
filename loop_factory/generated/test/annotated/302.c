int main1(){
  int qe, ku, hz, j9, t;
  qe=(1%24)+8;
  ku=qe;
  hz=0;
  j9=13;
  t=ku;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hz >= 0;
  loop invariant t == ((hz/4) + 1) * qe - 2 * (hz/4) * ((hz/4) - 1);
  loop invariant hz*hz - (2*qe + 4)*hz + 8*t - 72 == 0;
  loop invariant hz % 4 == 0;
  loop invariant t == 9 + 11*(hz/4) - 2*(hz/4)*(hz/4);
  loop assigns hz, t, j9;
*/
while (1) {
      if (!(hz<qe)) {
          break;
      }
      j9 = qe-hz;
      hz += 4;
      t = t + j9;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hz >= 0;
  loop invariant ku >= 0;
  loop assigns hz, ku;
*/
while (1) {
      if (!(hz<qe)) {
          break;
      }
      ku = (qe)+(-(hz));
      ku -= ku;
      hz++;
  }
}