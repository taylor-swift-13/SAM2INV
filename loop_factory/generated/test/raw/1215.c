int main1(){
  int i, qab, hf, xq, hz, v;

  i=1+8;
  qab=0;
  hf=1;
  xq=6;
  hz=0;
  v=12;

  while (1) {
      if (!(hz<=i)) {
          break;
      }
      qab += hf;
      hz++;
      hf = hf + xq;
      v = v+qab+qab;
      xq += 6;
  }

}
