int main1(){
  int htg, uc1, x2, wo;
  htg=93;
  uc1=5;
  x2=0;
  wo=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 5 <= uc1 <= htg + 1;
  loop invariant x2 == ((uc1 - 1) * uc1 * (2 * uc1 - 1)) / 6 - 30;
  loop invariant wo == uc1 * (uc1 + 1) / 2 - 20;
  loop invariant wo  == -5 + 5 * (uc1 - 5) + ((uc1 - 5) * (uc1 - 4)) / 2;
  loop invariant x2 == 25*(uc1-5) + 5*(uc1-5)*(uc1-6) + ((uc1-6)*(uc1-5)*(2*(uc1-5)-1))/6;
  loop invariant x2 == (((uc1 - 1) * uc1 * (2 * uc1 - 1)) / 6) - 30;
  loop invariant wo == (uc1 * (uc1 + 1)) / 2 - 20;
  loop invariant 2*wo == uc1*uc1 + uc1 - 40;
  loop assigns x2, uc1, wo;
*/
while (uc1<=htg) {
      x2 = x2+uc1*uc1;
      uc1++;
      wo = wo + uc1;
  }
}