int main1(){
  int ut, c, cz, y9, am, hq, sm2, v, tjcl;
  ut=1-1;
  c=3;
  cz=13;
  y9=0;
  am=0;
  hq=ut;
  sm2=ut;
  v=ut;
  tjcl=1+3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (cz + y9 == 13);
  loop invariant (am == c - 3);
  loop invariant ((c - 3) - 2 * v) >= 0;
  loop invariant ((c - 3) - 2 * v) <= 1;
  loop invariant tjcl == 4;
  loop invariant ut == 0;
  loop invariant sm2 == ut + 2*am;
  loop invariant hq == ut - am;
  loop invariant 0 <= cz;
  loop invariant 0 <= y9;
  loop invariant am >= 0;
  loop invariant v >= ut;
  loop invariant sm2 == 2*am;
  loop invariant v >= 0;
  loop invariant v <= am;
  loop assigns cz, y9, c, sm2, v, hq, am, tjcl;
*/
while (1) {
      if (!(c<ut)) {
          break;
      }
      if (c%2==0) {
          if (cz>0) {
              cz = cz - 1;
              y9++;
          }
      }
      else {
          if (y9>0) {
              y9 -= 1;
              cz += 1;
          }
      }
      c = c + 1;
      sm2 += 2;
      v = v+(c%2);
      hq -= 1;
      am += 1;
      if (c+6<=am+ut) {
          tjcl = tjcl + 1;
      }
  }
}