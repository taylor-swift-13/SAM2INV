int main1(){
  int aq, sg, mu;
  aq=0;
  sg=68;
  mu=34;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sg + aq == 68;
  loop invariant mu >= 0;
  loop invariant (aq + mu == 34);
  loop assigns aq, sg, mu;
*/
while (1) {
      if (!(mu>0)) {
          break;
      }
      sg = sg - 1;
      mu -= 1;
      aq = aq + 1;
  }
}