int main1(){
  int cq;
  cq=(1%28)+10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 1 <= cq && cq <= 11 && (cq == 11 || cq == 1);
  loop assigns cq;
*/
while (cq>cq) {
      cq -= cq;
      cq += 1;
  }
}