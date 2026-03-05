int main1(int t){
  int rgj, rxd;
  rgj=(t%10)+11;
  rxd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t >= \at(t, Pre);
  loop invariant 0 <= rxd;
  loop invariant rxd <= 3;
  loop invariant rgj == \at(t, Pre) % 10 + 11;
  loop assigns rxd, t;
*/
while (rxd<rgj) {
      rxd = (rxd+1)%3;
      rxd++;
      t += rxd;
  }
}