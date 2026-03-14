int main1(){
  int qc, wxhm, l, i4;
  qc=-2;
  wxhm=0;
  l=(1%28)+10;
  i4=20;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l + (wxhm * (wxhm - 1)) / 2 == 11;
  loop invariant wxhm >= 0;
  loop invariant qc == -2;
  loop invariant i4 >= 0;
  loop invariant l >= 0;
  loop assigns l, i4, wxhm;
*/
while (l>wxhm) {
      l -= wxhm;
      i4 += qc;
      wxhm += 1;
      i4 = (i4)+(i4*i4);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wxhm >= 0;
  loop invariant qc == -2;
  loop assigns wxhm;
*/
while (1) {
      if (!(wxhm<=qc-1)) {
          break;
      }
      wxhm += 1;
  }
}