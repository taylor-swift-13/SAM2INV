int main1(){
  int i14, fa, nj5;
  i14=55;
  fa=i14;
  nj5=i14;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fa == 55;
  loop invariant i14 == 55;
  loop invariant nj5 >= 55 && (nj5 == 55 || (nj5 % 2) == 0);
  loop invariant (nj5 + 2) % 57 == 0;
  loop assigns nj5;
*/
while (fa>=4) {
      nj5 += 1;
      nj5 = nj5 + nj5;
  }
}