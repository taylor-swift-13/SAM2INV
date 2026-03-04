int main1(){
  int pj;
  pj=(1%15)+3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= pj;
  loop invariant pj <= (1%15)+3;
  loop invariant pj == 0 || pj == 1 || pj == 2 || pj == 3 || pj == (1%15)+3;
  loop invariant 0 <= ( (1 % 15) + 3 - pj );
  loop invariant 0 <= pj <= 4;
  loop invariant pj >= 0;
  loop assigns pj;
*/
while (pj!=0) {
      pj = pj - 1;
  }
}