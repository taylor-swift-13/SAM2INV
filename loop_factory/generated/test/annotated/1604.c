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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nc == dm6r;
  loop invariant dm6r == 15;
  loop invariant dm07 == 3 + 2 * nc * v7 + ((v7 + 1) / 2);
  loop invariant 0 <= qvav;
  loop invariant qvav <= v7;
  loop invariant 3 <= jx;
  loop invariant jx <= 3 + v7;
  loop invariant 2 <= voo;
  loop invariant voo <= dm6r;
  loop invariant voo == v7 + 2;
  loop invariant (jx - qvav - y2 == 0);
  loop invariant (0 <= y2 && y2 <= dm07);
  loop invariant dm07 >= 3;
  loop assigns y2, qvav, jx, voo, v7, dm07;
*/
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