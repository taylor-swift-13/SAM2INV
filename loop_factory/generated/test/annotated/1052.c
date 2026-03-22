int main1(){
  int i6, lhk, r9, bb, i94, x6;
  i6=67;
  lhk=-3;
  r9=0;
  bb=0;
  i94=0;
  x6=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bb <= i6;
  loop invariant i94 == bb;
  loop invariant r9 == bb;
  loop invariant x6 == -5 + lhk * bb;
  loop invariant i6 == 67;
  loop invariant lhk == -3;
  loop invariant 0 <= bb;
  loop assigns bb, i94, r9, x6;
*/
while (bb<i6) {
      r9 = r9 + 1;
      x6 = x6 + lhk;
      i94++;
      bb++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i6 >= 0;
  loop invariant bb >= 0;
  loop invariant i94 >= 0;
  loop invariant x6 <= 0;
  loop assigns i6, bb, i94;
*/
while (i6<=x6-1) {
      i6 = i6 + 1;
      bb++;
      i94 = i94+(bb%8);
  }
}