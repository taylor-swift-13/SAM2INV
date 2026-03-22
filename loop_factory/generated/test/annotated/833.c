int main1(){
  int a, ms2, xe, eay, jdk2, ab;
  a=1*3;
  ms2=a+4;
  xe=6;
  eay=1;
  jdk2=ms2;
  ab=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == 3;
  loop invariant ab == 3;
  loop invariant eay >= 1;
  loop invariant xe >= 6;
  loop invariant jdk2 >= 1;
  loop invariant jdk2 >= a;
  loop invariant (15*eay) == (2*xe + 3);
  loop assigns xe, eay, jdk2;
*/
while (1) {
      if (!(jdk2<a)) {
          break;
      }
      xe = xe*ab+3;
      eay = eay*ab;
      jdk2 = a;
  }
}