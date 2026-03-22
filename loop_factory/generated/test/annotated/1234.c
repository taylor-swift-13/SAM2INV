int main1(){
  int hdkj, rnb, o0, dm, a03, q, hj0;
  hdkj=(1%24)+8;
  rnb=1;
  o0=0;
  dm=4;
  a03=13;
  q=rnb;
  hj0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o0 == ((q - 1) * (2 * q * q + 29 * q - 42)) / 6;
  loop invariant a03 == 2 * q + 11;
  loop invariant dm == q * q + 10 * q - 7;
  loop invariant hj0 <= 3 * (q - 1);
  loop invariant q <= hdkj + 1;
  loop invariant o0 >= 0;
  loop invariant dm >= 4;
  loop invariant hj0 >= 0;
  loop assigns o0, dm, a03, q, hj0;
*/
while (1) {
      if (q>hdkj) {
          break;
      }
      o0 = o0 + dm;
      dm += a03;
      a03 = (2)+(a03);
      q += 1;
      hj0 = hj0+(o0%4);
  }
}