int main1(){
  int i, qab, hf, xq, hz, v;
  i=1+8;
  qab=0;
  hf=1;
  xq=6;
  hz=0;
  v=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qab == hz*hz*hz;
  loop invariant xq == 6*(hz + 1);
  loop invariant hf == 3*hz*hz + 3*hz + 1;
  loop invariant v == 12 + (hz*hz*(hz+1)*(hz+1))/2;
  loop invariant 0 <= hz;
  loop invariant hz <= i+1;
  loop assigns qab, hz, hf, v, xq;
*/
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