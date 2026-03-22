int main1(int m){
  int qt, p, hsi, rws;
  qt=(m%28)+13;
  p=qt;
  hsi=(m%20)+10;
  rws=(m%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p >= (m%28) + 13;
  loop invariant hsi + rws + p == ((\at(m,Pre)%20) + 10) + ((\at(m,Pre)%15) + 8) + ((\at(m,Pre)%28) + 13);
  loop invariant hsi + rws + p == (m % 20) + (m % 15) + (m % 28) + 31;
  loop invariant hsi + rws + (p - qt) == (m % 20) + 10 + (m % 15) + 8;
  loop assigns p, hsi, rws;
*/
while (1) {
      if (!(hsi>0&&rws>0)) {
          break;
      }
      if (!(!(p%2==0))) {
          hsi--;
      }
      else {
          rws--;
      }
      p++;
  }
}