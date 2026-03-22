int main1(){
  int x, h59, pjq, wq;
  x=25;
  h59=0;
  pjq=0;
  wq=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wq == 5 - h59;
  loop invariant 0 <= h59;
  loop invariant h59 <= x;
  loop invariant pjq == (13*h59 - h59*h59) / 2;
  loop invariant 0 <= pjq;
  loop assigns pjq, h59, wq;
*/
while (1) {
      if (!(h59<x&&wq>0)) {
          break;
      }
      pjq += wq;
      h59++;
      pjq++;
      wq -= 1;
  }
}