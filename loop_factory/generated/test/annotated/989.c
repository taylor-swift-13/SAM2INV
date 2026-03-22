int main1(int j){
  int ix, cj, qcsy, lt, ger, qc;
  ix=67;
  cj=0;
  qcsy=0;
  lt=16;
  ger=ix;
  qc=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qcsy % 6 == 0;
  loop invariant lt == 16 + 2*(qcsy/6);
  loop invariant ger == 67 + (qcsy/6)*(qcsy/6) + 17*(qcsy/6);
  loop invariant qc == 4 + 3*(qcsy/6)*(qcsy/6) + 3*(qcsy/6);
  loop invariant 0 <= qcsy;
  loop invariant cj == 0;
  loop assigns lt, qcsy, ger, qc, j;
*/
while (qcsy<ix) {
      lt += 2;
      qcsy = qcsy+6+cj%2;
      ger += lt;
      qc += qcsy;
      j = lt+ger+qc;
  }
}