int main1(int f){
  int ge, ko, m5n, wi;
  ge=f-9;
  ko=ge;
  m5n=0;
  wi=ko;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (f - \at(f, Pre)) % 2 == 0;
  loop invariant f >= \at(f, Pre);
  loop invariant wi >= \at(f, Pre) - 9;
  loop invariant 0 <= m5n && (m5n <= ge || ge <= 0);
  loop invariant ge + 9 == \at(f, Pre);
  loop assigns m5n, f, wi;
*/
while (1) {
      if (!(m5n<ge)) {
          break;
      }
      if (m5n<ge/2) {
          m5n += 2;
      }
      else {
          m5n += 1;
      }
      f += 2;
      wi += m5n;
  }
}