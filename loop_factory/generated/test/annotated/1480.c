int main1(){
  int p, bpq, a;
  p=(1%18)+5;
  bpq=(1%15)+3;
  a=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bpq == p - 2;
  loop invariant 2*a == -p*p + 5*p + 18;
  loop invariant p >= 0;
  loop assigns a, p, bpq;
*/
while (1) {
      if (!(p!=0)) {
          break;
      }
      bpq = bpq - 1;
      p -= 1;
      a = a + bpq;
  }
}