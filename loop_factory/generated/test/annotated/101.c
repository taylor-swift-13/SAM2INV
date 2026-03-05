int main1(){
  int kvbt, otk, e9, vj;
  kvbt=12;
  otk=0;
  e9=0;
  vj=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e9 == 3*otk;
  loop invariant 0 <= otk;
  loop invariant otk <= kvbt;
  loop invariant kvbt == 12;
  loop invariant vj == e9 + 3;
  loop assigns e9, vj, otk;
*/
while (otk<kvbt) {
      e9 = e9 + 3;
      vj = vj + 3;
      otk++;
  }
}