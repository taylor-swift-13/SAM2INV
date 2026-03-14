int main1(){
  int qe, ku, hz, j9, t;

  qe=(1%24)+8;
  ku=qe;
  hz=0;
  j9=13;
  t=ku;

  while (1) {
      if (!(hz<qe)) {
          break;
      }
      j9 = qe-hz;
      hz += 4;
      t = t + j9;
  }

  while (1) {
      if (!(hz<qe)) {
          break;
      }
      ku = (qe)+(-(hz));
      ku -= ku;
      hz++;
  }

}
