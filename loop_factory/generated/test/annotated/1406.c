int main1(){
  int cf, uuml, j6, l;
  cf=57;
  uuml=0;
  j6=0;
  l=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j6 == l * (1 + uuml);
  loop invariant uuml == 0;
  loop invariant 0 <= l <= cf;
  loop assigns l, j6;
*/
while (1) {
      if (!(l<cf)) {
          break;
      }
      l = l + 1;
      j6++;
      j6 = j6 + uuml;
  }
}