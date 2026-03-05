int main1(){
  int s6l, g;
  s6l=(1%30)+13;
  g=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g % 2 == 1;
  loop invariant g >= 1;
  loop invariant s6l == 14;
  loop invariant g <= s6l + 1;
  loop assigns g, s6l;
*/
while (g<s6l) {
      g += 2;
  }
}