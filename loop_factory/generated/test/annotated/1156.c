int main1(){
  int d, qe, nr, whfj, pg;
  d=1*4;
  qe=(1%40)+2;
  nr=0;
  whfj=d;
  pg=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == 4;
  loop invariant whfj % d == 0;
  loop invariant nr >= 0;
  loop invariant pg >= 0;
  loop invariant 0 < qe;
  loop invariant qe * qe >= d;
  loop invariant 0 <= whfj;
  loop assigns nr, pg, qe, whfj;
*/
while (1) {
      if (!(qe!=nr)) {
          break;
      }
      nr = qe;
      pg = pg+(nr%2);
      qe = (qe+d/qe)/2;
      whfj = whfj*4;
  }
}