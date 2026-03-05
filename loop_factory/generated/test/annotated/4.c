int main1(){
  int pj;
  pj=(1%15)+3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pj >= 0;
  loop invariant pj <= 4;
  loop assigns pj;
*/
while (pj!=0) {
      pj = pj - 1;
  }
}