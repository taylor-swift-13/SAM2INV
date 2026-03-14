int main1(int k,int a){
  int m1h, m3c9, rf, k2;
  m1h=187;
  m3c9=1;
  rf=0;
  k2=k;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rf == (m3c9 - 1) * (m3c9 - 1);
  loop invariant k2 == \at(k,Pre) + (m3c9 - 1);
  loop invariant k - \at(k,Pre) == ((m3c9 - 1) * m3c9 * (2 * m3c9 - 1)) / 6;
  loop invariant rf == (m3c9 - 1) * (m3c9 - 1) &&
                   k2 == \at(k, Pre) + (m3c9 - 1);
  loop invariant 1 <= m3c9 <= m1h + 1;
  loop assigns rf, m3c9, k2, k;
*/
while (m3c9<=m1h) {
      rf = rf+2*m3c9-1;
      m3c9++;
      k2++;
      k += rf;
  }
}