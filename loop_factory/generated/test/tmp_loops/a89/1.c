int main1(){
  int dm6r, voo, y2, jx, qvav, dm07, v7, nc;

  dm6r=(1%33)+14;
  voo=2;
  y2=3;
  jx=3;
  qvav=0;
  dm07=3;
  v7=0;
  nc=dm6r;

  while (voo<=dm6r-1) {
      if (voo%3==0) {
          if (y2>0) {
              y2--;
              qvav += 1;
          }
      }
      else {
          if (y2<dm07) {
              y2 = y2 + 1;
              jx++;
          }
      }
      voo++;
      v7 += 1;
      dm07 = dm07+(voo%2);
      dm07 = dm07+nc+nc;
  }

}
