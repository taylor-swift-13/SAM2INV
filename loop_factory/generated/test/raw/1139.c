int main1(){
  int jrq, i, gc, c, w66;

  jrq=(1%16)+7;
  i=0;
  gc=3;
  c=jrq;
  w66=12;

  while (i<jrq) {
      c = c + w66;
      w66 += gc;
      i += 4;
  }

  while (1) {
      jrq = jrq + jrq;
      jrq = jrq + w66;
      gc++;
      if (gc>=i) {
          break;
      }
  }

}
