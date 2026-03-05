int main1(){
  int eur;
  eur=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eur >= 0;
  loop invariant eur <= (1 % 20 + 5);
  loop invariant eur % 2 == 0;
  loop assigns eur;
*/
while (eur>0) {
      if (eur>0) {
          if (eur>0) {
              eur = eur - 1;
              eur = eur - 1;
              eur = eur - 1;
          }
      }
      eur += 1;
  }
}