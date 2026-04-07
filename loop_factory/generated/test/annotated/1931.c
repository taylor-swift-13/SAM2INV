int main1(int a){
  int sp, au9, i;
  sp=a+24;
  au9=0;
  i=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre) + (au9 * (au9 + 1)) / 2;
  loop invariant i == 3 + au9 * \at(a, Pre) + (au9 * (au9 - 1) * (au9 + 1)) / 6;
  loop invariant sp == \at(a, Pre) + 24;
  loop invariant au9 >= 0;
  loop invariant 0 <= au9 && (sp >= 0 ==> au9 <= sp);
  loop invariant 2 * (a - \at(a, Pre)) == au9 * (au9 + 1);
  loop invariant 6 * (i - 3 - au9 * \at(a, Pre)) == (au9 - 1) * au9 * (au9 + 1);
  loop invariant (a - \at(a, Pre) == (au9*(au9 + 1))/2);
  loop invariant (au9 >= 0);
  loop invariant 0 <= au9;
  loop assigns a, au9, i;
*/
while (au9 < sp) {
      i = i + a;
      au9++;
      a = a + au9;
  }
}