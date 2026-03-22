int main1(int i){
  int m16c, sry, rcj, uo, xq, fup, fbfa, c;
  m16c=i+19;
  sry=m16c;
  rcj=sry;
  uo=0;
  xq=7;
  fup=-6;
  fbfa=10;
  c=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m16c == \at(i, Pre) + 19;
  loop invariant sry >= m16c;
  loop invariant rcj <= sry;
  loop invariant fbfa == 10 + (sry - m16c);
  loop invariant xq >= 7;
  loop invariant c >= 12;
  loop invariant uo >= 0;
  loop invariant i >= \at(i, Pre);
  loop invariant sry >= \at(i,Pre) + 19;
  loop invariant fbfa == sry - \at(i,Pre) - 9;
  loop invariant fup == -6 + 3*(sry - \at(i,Pre) - 19);
  loop invariant rcj >= \at(i,Pre) + 19;
  loop invariant fbfa - c == -2;
  loop invariant rcj + uo == sry;
  loop invariant c == sry - \at(i,Pre) - 7;
  loop invariant uo <= sry - \at(i,Pre) - 19;
  loop invariant fbfa >= 10;
  loop invariant fup >= -6;
  loop invariant rcj >= m16c;
  loop invariant fup == -6 + 3*(sry - m16c);
  loop invariant xq <= 7 + (sry - m16c);
  loop invariant 0 <= uo <= sry - \at(i, Pre) - 19;
  loop invariant 7 <= xq <= sry - \at(i, Pre) - 12;
  loop assigns rcj, uo, xq, c, fbfa, fup, i, sry;
*/
while (sry-3>=0) {
      if (sry%4==2) {
          rcj++;
      }
      else {
          uo = uo + 1;
      }
      if (sry%4==3) {
          xq += 1;
      }
      else {
      }
      c = c + 1;
      fbfa += 2;
      fup = (2)+(fup);
      i += uo;
      fbfa--;
      fup++;
      sry += 1;
  }
}