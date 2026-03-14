int main1(){
  int u, b, rp8, v6, q;
  u=40;
  b=-5;
  rp8=18;
  v6=1;
  q=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 40;
  loop invariant b == q - 5;
  loop invariant rp8 <= 18;
  loop invariant q == v6 - 1;
  loop assigns rp8, b, q, v6;
*/
while (rp8>0&&v6<=u) {
      if (!(rp8<=v6)) {
          rp8 = 0;
      }
      else {
          rp8 -= v6;
      }
      b += 1;
      q += 1;
      v6++;
  }
}