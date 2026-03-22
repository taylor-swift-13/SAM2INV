int main1(int j,int q){
  int f, nbo, y5;
  f=(j%15)+12;
  nbo=0;
  y5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= y5;
  loop invariant nbo == y5 * j;
  loop assigns y5, nbo;
*/
while (1) {
      if (!(y5<=f-1)) {
          break;
      }
      y5 = y5 + 1;
      nbo += j;
  }
}