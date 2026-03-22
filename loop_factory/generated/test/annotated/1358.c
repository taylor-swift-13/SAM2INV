int main1(){
  int a1o, zi9, aq, vsax;
  a1o=1+7;
  zi9=1;
  aq=a1o;
  vsax=zi9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aq == 8 * zi9;
  loop invariant vsax == -15 + 16 * zi9;
  loop invariant aq == a1o * zi9;
  loop invariant vsax == a1o * (2 * zi9 - 2) + 1;
  loop assigns aq, vsax, zi9;
*/
while (zi9<=a1o-1) {
      aq = aq*2;
      vsax += aq;
      zi9 = zi9*2;
  }
}