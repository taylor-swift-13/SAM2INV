int main1(){
  int ay, z, l6, hw2;
  ay=(1%22)+19;
  z=4;
  l6=2;
  hw2=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l6 == 2 + 5*(z - 4);
  loop invariant hw2 == 7 + 5*(z - 4);
  loop invariant ay == (1 % 22) + 19;
  loop invariant 4 <= z <= ay;
  loop assigns l6, hw2, z;
*/
while (z<ay) {
      l6 = l6 + 5;
      hw2 = hw2 + 5;
      z += 1;
  }
}