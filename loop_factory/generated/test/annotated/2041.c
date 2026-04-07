int main1(){
  int hw, l, ugh, sik, hz, en;
  hw=1-5;
  l=0;
  ugh=10;
  sik=hw;
  hz=l;
  en=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (en - 3 * l == 0);
  loop invariant (sik == hw);
  loop invariant (l >= 0);
  loop invariant (0 <= en % 9 && en % 9 <= 6);
  loop invariant (0 <= hz && hz <= 6 * l);
  loop invariant ugh == 10 + (sik % 4) * l;
  loop invariant (l % 3 == 0 || l % 3 == 1) ==> hz == 9 * (l / 3);
  loop invariant (l % 3 == 2) ==> hz == 9 * (l / 3) + 3;
  loop assigns ugh, hz, l, en;
*/
while (l < hw) {
      ugh = ugh+(sik%4);
      hz = hz+(en%9);
      l = l + 1;
      en = en + 3;
  }
}