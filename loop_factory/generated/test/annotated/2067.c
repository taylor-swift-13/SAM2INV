int main1(){
  int z1z, x5, j, w7, c;
  z1z=1;
  x5=0;
  j=-1;
  w7=-3;
  c=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w7 == -3 + c * x5;
  loop invariant j == -1 - 3 * x5 + (c * x5 * (x5 - 1)) / 2;
  loop invariant 0 <= x5;
  loop invariant x5 <= z1z;
  loop invariant j == (x5 * x5 - 4 * x5 - 1);
  loop invariant w7 - c * x5 == -3;
  loop invariant j == -1 + x5 * w7 - c * ((x5 * (x5 + 1)) / 2);
  loop invariant c == 2;
  loop invariant z1z == 1;
  loop assigns j, x5, w7;
*/
while (x5 < z1z) {
      j += w7;
      x5 += 1;
      w7 = w7 + c;
  }
}