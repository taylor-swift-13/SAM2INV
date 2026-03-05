int main1(int i,int a){
  int jjoy;
  jjoy=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant 0 <= jjoy <= 1;
  loop invariant jjoy == 0 || jjoy == 1;
  loop assigns i, jjoy;
*/
while (jjoy!=jjoy) {
      if (jjoy>jjoy) {
          jjoy -= jjoy;
          jjoy -= jjoy;
          jjoy -= jjoy;
      }
      else {
          jjoy -= jjoy;
          jjoy -= jjoy;
          jjoy -= jjoy;
      }
      i = i+jjoy-jjoy;
  }
}