int main1(int z,int f){
  int x0, jyyr;
  x0=f*3;
  jyyr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= jyyr;
  loop invariant (x0 >= 0) ==> (jyyr <= x0);
  loop invariant x0 == (3 * \at(f, Pre));
  loop assigns jyyr;
*/
while (1) {
      if (!(jyyr+1<=x0)) {
          break;
      }
      jyyr = jyyr + 1;
  }
}