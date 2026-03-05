int main1(){
  int rsq, o, tiv;
  rsq=24;
  o=rsq;
  tiv=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rsq == 24;
  loop invariant tiv == 0 || tiv == rsq + 1;
  loop invariant o == rsq;
  loop assigns tiv;
*/
while (o-1>=0) {
      tiv = rsq-tiv;
      tiv = tiv + 1;
  }
}