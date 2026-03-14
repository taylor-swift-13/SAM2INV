int main1(){
  int by9, j3i, u1y;
  by9=1*2;
  j3i=0;
  u1y=by9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (j3i <= by9/2) ==> (u1y == by9 + 6*j3i);
  loop invariant (j3i > by9/2) ==> (u1y == by9 + 6*j3i + 2*(j3i - by9/2));
  loop invariant by9 == 2;
  loop invariant 0 <= j3i <= by9;
  loop assigns u1y, j3i;
*/
while (j3i<by9) {
      if (j3i>=by9/2) {
          u1y += 2;
      }
      j3i++;
      u1y += 6;
  }
}