int main1(){
  int c9;
  c9=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c9 == -8 || c9 == 4;
  loop assigns c9;
*/
while (c9!=0&&c9!=0) {
      if (c9>c9) {
          c9 -= c9;
      }
      else {
          c9 -= c9;
      }
      c9 += 4;
  }
}