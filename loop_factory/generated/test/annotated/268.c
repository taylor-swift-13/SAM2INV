int main1(int q){
  int lo, hu, w, oq;
  lo=14;
  hu=0;
  w=4;
  oq=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == 4 + 7*hu;
  loop invariant oq == 11 + 7*hu;
  loop invariant 0 <= hu;
  loop invariant hu <= lo;
  loop invariant q == \at(q, Pre);
  loop assigns hu, w, oq;
*/
while (hu<lo) {
      w = w + 7;
      oq = oq + 7;
      hu += 1;
  }
}