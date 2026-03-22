int main1(){
  int ff6, gw79, fd;
  ff6=(1%20)+5;
  gw79=(1%20)+5;
  fd=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ff6 == gw79;
  loop invariant gw79 == fd;
  loop invariant ff6 >= 0;
  loop assigns ff6, gw79, fd;
*/
while (ff6>=1) {
      if (gw79>0) {
          if (fd>0) {
              ff6--;
              gw79 -= 1;
              fd -= 1;
          }
      }
  }
}