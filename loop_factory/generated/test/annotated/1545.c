int main1(int i){
  int t, o, bjr, h, qsv, xw, c2, k;
  t=67;
  o=0;
  bjr=0;
  h=o;
  qsv=1;
  xw=i;
  c2=0;
  k=t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre) + o;
  loop invariant o <= t;
  loop invariant t == 67;
  loop invariant qsv - c2 == 1 + o;
  loop invariant k + h == 67 + o * \at(i, Pre) + (o * (o - 1)) / 2;
  loop invariant \at(i, Pre) - o <= xw;
  loop invariant xw <= \at(i, Pre);
  loop invariant (bjr == 0) || (bjr == 1);
  loop assigns o, i, k, h, bjr, c2, qsv, xw;
*/
while (1) {
      if (!(o < t)) {
          break;
      }
      o = o + 1;
      if ((bjr == 0)) {
          k = k + i;
      }
      if ((bjr == 1)) {
          h = h + i;
      }
      if (!(!(((i % 2) != 0)))) {
          bjr = 0;
      }
      else {
          bjr = 1;
      }
      i = i + 1;
      c2 = c2 + k;
      qsv = qsv + k;
      xw += bjr;
      qsv++;
      xw = xw - 1;
  }
}