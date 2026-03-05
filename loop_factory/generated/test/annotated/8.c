int main1(){
  int w6j;
  w6j=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w6j == 16;
  loop assigns w6j;
*/
while (w6j>0) {
      w6j = w6j + 1;
      w6j--;
  }
}