int main1(){
  int eh2, bw, aw, j1z;
  eh2=1;
  bw=1;
  aw=0;
  j1z=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aw == j1z;
  loop invariant 0 <= j1z <= eh2;
  loop assigns aw, j1z;
*/
while (1) {
      if (!(j1z<eh2)) {
          break;
      }
      aw = aw + 1;
      j1z++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j1z <= bw;
  loop invariant aw >= 0;
  loop invariant aw <= 1;
  loop invariant (aw == 0) ==> (j1z >= 2);
  loop invariant j1z >= bw;
  loop invariant ((j1z != 1) ==> (aw == 0));
  loop assigns aw, j1z;
*/
while (1) {
      aw -= aw;
      j1z++;
      if (j1z>=bw) {
          break;
      }
  }
}