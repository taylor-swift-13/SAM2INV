int main1(){
  int x;
  x=17;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 17;
  loop assigns x;
*/
while (x>0) {
      x = x + 1;
      x--;
  }
}