int main1(){
  int g, q, rmn;
  g=1*2;
  q=g;
  rmn=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 2;
  loop invariant 0 <= q <= 2;
  loop invariant rmn == 2 + 4*(2 - q) - ((2 - q) * (1 - q)) / 2;
  loop assigns rmn, q;
*/
for (; q-1>=0; q = q - 1) {
      rmn = rmn + q;
      rmn += 2;
  }
}