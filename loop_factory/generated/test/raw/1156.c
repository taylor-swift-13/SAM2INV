int main1(){
  int d, qe, nr, whfj, pg;

  d=1*4;
  qe=(1%40)+2;
  nr=0;
  whfj=d;
  pg=0;

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
