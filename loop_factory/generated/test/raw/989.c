int main1(int j){
  int ix, cj, qcsy, lt, ger, qc;

  ix=67;
  cj=0;
  qcsy=0;
  lt=16;
  ger=ix;
  qc=4;

  while (qcsy<ix) {
      lt += 2;
      qcsy = qcsy+6+cj%2;
      ger += lt;
      qc += qcsy;
      j = lt+ger+qc;
  }

}
