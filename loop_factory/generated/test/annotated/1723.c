int main1(int m){
  int b9g, trv, wc, y9r, km;
  b9g=(m%8)+15;
  trv=0;
  wc=0;
  y9r=b9g;
  km=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y9r == b9g + trv * m;
  loop invariant km == -3 + trv * m;
  loop invariant wc == trv * m;
  loop invariant b9g == (m % 8) + 15;
  loop invariant 0 <= trv <= b9g;
  loop invariant b9g == (\at(m, Pre) % 8) + 15;
  loop assigns y9r, km, trv, wc;
*/
while (1) {
      if (!(trv < b9g)) {
          break;
      }
      y9r = y9r + m;
      km = km + m;
      trv = trv + 1;
      wc = wc + m;
  }
}