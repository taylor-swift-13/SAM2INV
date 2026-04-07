int main1(){
  int mjb, yko, jty, qmb;

  mjb=1;
  yko=0;
  jty=0;
  qmb=0;

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
