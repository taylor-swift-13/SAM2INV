int main1(){
  int k42, w, dvw, v89, vtc8, d02d, l, n5l, rd;
  k42=1*2;
  w=k42;
  dvw=13;
  v89=0;
  vtc8=11;
  d02d=k42;
  l=-5;
  n5l=w;
  rd=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rd - w == 9;
  loop invariant dvw >= 0;
  loop invariant v89 >= 0;
  loop invariant k42 == 2;
  loop invariant l == -5 + 11*(w - k42);
  loop invariant dvw + v89 == 13;
  loop invariant 0 <= w <= k42;
  loop invariant l >= -5;
  loop invariant vtc8 == 11;
  loop invariant rd >= 11;
  loop invariant n5l >= 2;
  loop assigns dvw, v89, w, n5l, d02d, l, rd;
*/
while (w<k42) {
      if (w%2==0) {
          if (dvw>0) {
              dvw -= 1;
              v89 = v89 + 1;
          }
      }
      else {
          if (v89>0) {
              v89--;
              dvw++;
          }
      }
      w += 1;
      n5l = n5l + v89;
      d02d += l;
      l = l + vtc8;
      rd++;
      d02d = rd-d02d;
  }
}