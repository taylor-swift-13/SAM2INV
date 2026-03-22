int main1(int t){
  int ul, g3j5, tv;
  ul=38;
  g3j5=ul;
  tv=ul;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tv == 38 + ((38 - g3j5) * (39 + g3j5)) / 2;
  loop invariant g3j5 >= 0;
  loop invariant g3j5 <= 38;
  loop assigns tv, g3j5;
*/
while (g3j5>=1) {
      tv = tv + g3j5;
      g3j5 -= 1;
  }
}