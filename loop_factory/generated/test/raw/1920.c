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
