int main1(){
  int pu;
  pu=14;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pu == 14;
  loop assigns pu;
*/
while (pu>0) {
      pu++;
      pu -= 1;
  }
}