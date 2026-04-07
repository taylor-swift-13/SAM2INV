int main1(int b){
  int z7x, ordi, uou, j;
  z7x=b*2;
  ordi=0;
  uou=0;
  j=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z7x == \at(b, Pre) * 2;
  loop invariant (b - \at(b, Pre)) == 2 * j;
  loop invariant j >= 0;
  loop invariant 0 <= ordi;
  loop invariant (ordi != z7x) ==> (uou == (ordi * ordi));
  loop invariant (ordi == z7x) ==> (j == uou && (b - \at(b, Pre)) == (2 * uou));
  loop invariant (ordi == 0 || ordi == z7x);
  loop invariant (ordi == 0) ==> (uou == 0 && j == 0);
  loop assigns uou, b, j, ordi;
*/
while (ordi < z7x) {
      uou = (ordi++, uou + (2*ordi - 1));
      b = b+uou+uou;
      j = j + uou;
      ordi = z7x;
  }
}