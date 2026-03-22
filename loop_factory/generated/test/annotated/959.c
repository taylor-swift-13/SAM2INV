int main1(){
  int yvo, pgn, w2x8, w6;
  yvo=1+8;
  pgn=yvo;
  w2x8=-12914;
  w6=pgn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pgn == yvo;
  loop invariant w2x8 == -12914 + 5 * ((w6 - 9) / 10) * ((w6 - 9) / 10) + 5 * ((w6 - 9) / 10);
  loop invariant w6 % 10 == 9;
  loop assigns w2x8, w6;
*/
while (1) {
      if (!(w2x8+8<0)) {
          break;
      }
      w2x8 = w2x8+w6+1;
      w6 += 1;
      if (yvo<yvo+2) {
          w6 = w6 + pgn;
      }
  }
}