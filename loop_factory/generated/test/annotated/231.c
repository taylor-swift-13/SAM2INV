int main1(){
  int twfl, gwr;
  twfl=1;
  gwr=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant twfl == 1;
  loop invariant gwr % 2 == 1;
  loop invariant gwr <= 2*twfl + 1;
  loop assigns gwr;
*/
while (gwr<=twfl) {
      gwr += gwr;
      gwr = gwr + 1;
  }
}