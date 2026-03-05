int main1(){
  int tp;
  tp=(1%15)+3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= tp;
  loop invariant tp <= 4;
  loop assigns tp;
*/
while (tp!=0) {
      tp--;
  }
}