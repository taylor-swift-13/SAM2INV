int main1(int y){
  int gb, kx6x, z, i;
  gb=39;
  kx6x=0;
  z=gb;
  i=gb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (kx6x == 0 || kx6x == gb);
  loop invariant (kx6x == 0) ==> (z == gb);
  loop invariant (kx6x > 0) ==> (z == gb + y*y);
  loop invariant i >= gb;
  loop assigns z, i, kx6x;
*/
while (kx6x < gb) {
      z = (kx6x = kx6x + 1, z + kx6x * y * y);
      i = i*2+(z%5)+2;
      kx6x = gb;
  }
}