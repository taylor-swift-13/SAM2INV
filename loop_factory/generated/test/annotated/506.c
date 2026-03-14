int main1(int c){
  int s7, uzq5, str;
  s7=c+8;
  uzq5=c;
  str=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c - \at(c, Pre) == s7 * (uzq5 - \at(c, Pre));
  loop invariant str == 3 * (uzq5 - \at(c, Pre));
  loop invariant s7 == \at(c, Pre) + 8;
  loop invariant 0 <= uzq5 - \at(c, Pre) <= s7 - \at(c, Pre);
  loop assigns c, uzq5, str;
*/
while (uzq5<s7) {
      c += s7;
      uzq5 = uzq5 + 1;
      str = str + 3;
  }
}