int main1(){
  int bl, jcyt, pt, iy, qz8, qc;

  bl=41;
  jcyt=6;
  pt=0;
  iy=jcyt;
  qz8=0;
  qc=(1%6)+2;

  while (qz8<=bl-1) {
      pt = pt*qc+2;
      iy = iy*qc;
      qz8 = bl;
      if ((jcyt%2)==0) {
          qc += qc;
      }
      else {
          qc = qc%8;
      }
  }

}
