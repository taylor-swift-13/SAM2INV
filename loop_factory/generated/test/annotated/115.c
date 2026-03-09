int main1(){
  int f, aj2g, g, ya;
  f=1-7;
  aj2g=0;
  g=0;
  ya=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ya == 7 + 7*aj2g;
  loop invariant g == 7*aj2g;
  loop invariant f == 1 - 7;
  loop invariant 0 <= aj2g;
  loop invariant ya == g + 7;
  loop assigns aj2g, ya, g;
*/
while (aj2g<=f-1) {
      aj2g += 1;
      ya = ya + 7;
      g = g + 7;
  }
}