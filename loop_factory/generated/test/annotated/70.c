int main1(){
  int jx, b1;
  jx=1;
  b1=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jx == 1;
  loop invariant b1 <= 2*jx + 1;
  loop invariant (b1 == 0) || (b1 % 2 == 1);
  loop assigns b1;
*/
while (b1<=jx) {
      b1 = 2*b1;
      b1 = b1 + 1;
  }
}