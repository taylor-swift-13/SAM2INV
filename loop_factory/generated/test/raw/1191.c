int main1(){
  int mbyu, es, jr, d, so, bq, r8v;

  mbyu=(1%20)+13;
  es=mbyu+6;
  jr=-2;
  d=es;
  so=0;
  bq=mbyu;
  r8v=mbyu;

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
