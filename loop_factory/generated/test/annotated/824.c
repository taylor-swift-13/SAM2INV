int main1(){
  int b2, a8, c40a, z, zh2j, h;
  b2=1;
  a8=1;
  c40a=a8;
  z=a8;
  zh2j=0;
  h=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c40a == z*h - 2;
  loop invariant zh2j == 0 || zh2j == b2;
  loop invariant z > 0;
  loop invariant (h - 1) * c40a == (h + 3) * z - 4;
  loop invariant (b2 - zh2j) >= 0;
  loop assigns z, c40a, zh2j;
*/
while (zh2j<=b2-1) {
      z = z*h;
      c40a = c40a*h+4;
      zh2j = b2;
  }
}