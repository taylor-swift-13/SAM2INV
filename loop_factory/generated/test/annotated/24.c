int main1(int j,int i){
  int rv;
  rv=-11096;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre);
  loop invariant j <= \at(j, Pre);
  loop invariant rv <= -11096;
  loop assigns rv, j;
*/
while (rv<=-4) {
      rv = rv+rv+3;
      rv += 2;
      j += rv;
  }
}