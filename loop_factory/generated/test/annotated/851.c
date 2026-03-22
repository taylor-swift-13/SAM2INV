int main1(){
  int io, nm2, bj, s;
  io=1;
  nm2=io;
  bj=3;
  s=nm2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bj >= 3;
  loop invariant nm2 == 1;
  loop invariant io == 1;
  loop invariant s >= nm2;
  loop invariant bj >= s*s;
  loop assigns s, bj, nm2;
*/
while (1) {
      if (!(nm2>=2)) {
          break;
      }
      s++;
      bj = s*s;
      nm2 = 1;
  }
}