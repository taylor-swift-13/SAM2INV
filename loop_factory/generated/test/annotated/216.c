int main1(){
  int ab, w1j, edpz, mzk;
  ab=78;
  w1j=0;
  edpz=1;
  mzk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant edpz - mzk == 1;
  loop invariant 0 <= mzk;
  loop invariant mzk <= ab;
  loop invariant ab == 78;
  loop assigns edpz, mzk;
*/
while (mzk<ab) {
      mzk += 1;
      edpz = edpz + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w1j == 0;
  loop invariant ab == 78;
  loop invariant 0 <= mzk;
  loop invariant (mzk == edpz) || ((edpz - mzk) == 1);
  loop assigns ab, mzk;
*/
while (mzk<edpz) {
      ab = ab+w1j*mzk;
      mzk = edpz;
  }
}