int main1(int z){
  int ba, is, wy, h4, l;
  ba=(z%24)+20;
  is=0;
  wy=is;
  h4=z;
  l=ba;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == ba - is;
  loop invariant h4 == z * (is + 1);
  loop invariant wy == -is;
  loop invariant ba == (z % 24) + 20;
  loop invariant ba == ((\at(z,Pre)) % 24) + 20;
  loop assigns wy, is, l, h4;
*/
while (1) {
      if (!(is < ba)) {
          break;
      }
      wy--;
      is++;
      l--;
      h4 += z;
  }
}