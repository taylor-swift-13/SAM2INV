int main1(int v){
  int mgq, qt, k;
  mgq=(v%7)+15;
  qt=0;
  k=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == -6 + 3*qt;
  loop invariant v == \at(v, Pre) + qt;
  loop invariant mgq == (\at(v, Pre) % 7) + 15;
  loop invariant qt <= mgq;
  loop assigns k, v, qt;
*/
while (1) {
      if (!(qt<=mgq-1)) {
          break;
      }
      k = k + 3;
      v++;
      qt++;
  }
}