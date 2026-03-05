int main1(){
  int dk6;
  dk6=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (dk6 == 0) || (dk6 == 5);
  loop assigns dk6;
*/
while (dk6!=0&&dk6!=0) {
      if (dk6>dk6) {
          dk6 = dk6 - dk6;
      }
      else {
          dk6 = dk6 - dk6;
      }
      dk6 = dk6 + dk6;
      dk6 = dk6 - dk6;
  }
}