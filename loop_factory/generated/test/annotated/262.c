int main1(int l){
  int ap, df6, ghu, go, reu;
  ap=l;
  df6=0;
  ghu=0;
  go=0;
  reu=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant reu == df6 - 3;
  loop invariant go == df6 % 6;
  loop invariant ghu == df6 / 6;
  loop invariant 0 <= df6;
  loop invariant ap == l;
  loop assigns reu, go, ghu, df6;
*/
while (1) {
      if (!(df6<ap)) {
          break;
      }
      reu += 1;
      go++;
      if (go>=6) {
          go -= 6;
          ghu = ghu + 1;
      }
      df6++;
  }
}