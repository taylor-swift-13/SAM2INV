int main1(int m,int j){
  int e, gl6, grc;
  e=(m%34)+12;
  gl6=3;
  grc=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == (\at(m, Pre) % 34) + 12;
  loop invariant grc == -8;
  loop invariant gl6 == 3;
  loop invariant (j - \at(j, Pre)) % 8 == 0;
  loop invariant e == (m % 34) + 12;
  loop assigns grc, j;
*/
while (gl6<e) {
      grc += 2;
      grc -= 2;
      j += grc;
  }
}