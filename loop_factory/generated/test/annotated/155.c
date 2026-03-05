int main1(){
  int g8;
  g8=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g8 == 6 || g8 == 0;
  loop assigns g8;
*/
while (g8!=g8) {
      if (g8>g8) {
          g8 = g8 - g8;
          g8 = g8 + g8;
      }
      else {
          g8 = g8 - g8;
          g8 = g8 + g8;
      }
      g8 = g8 + g8;
  }
}