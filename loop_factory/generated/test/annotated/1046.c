int main1(){
  int ad, g, taxt, tt0, x9g;
  ad=1+14;
  g=1;
  taxt=0;
  tt0=0;
  x9g=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant taxt % 3 == 0;
  loop invariant x9g == 1 + ad * (taxt/3) - (3 * (taxt/3) * ((taxt/3) - 1)) / 2;
  loop invariant 0 <= taxt <= ad;
  loop invariant 0 <= tt0 <= ad;
  loop assigns taxt, tt0, x9g;
*/
while (taxt<ad) {
      tt0 = (ad)+(-(taxt));
      taxt = taxt + 3;
      x9g += tt0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x9g >= tt0;
  loop invariant taxt % 3 == 0;
  loop assigns x9g, taxt;
*/
while (1) {
      if (!(x9g<tt0)) {
          break;
      }
      x9g++;
      taxt = tt0-x9g;
      taxt = (taxt)+(-(taxt));
  }
}