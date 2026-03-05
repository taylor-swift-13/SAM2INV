int main1(int s){
  int sdq, eit, u4ud;
  sdq=(s%18)+6;
  eit=sdq;
  u4ud=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(s,Pre);
  loop invariant sdq == (\at(s,Pre) % 18) + 6;
  loop invariant eit <= sdq;
  loop invariant 0 <= u4ud <= 4;
  loop invariant (u4ud == 0) ==> (eit == sdq);
  loop invariant (\at(s, Pre) % 18) + 6 <= eit;
  loop assigns u4ud, eit;
*/
while (eit<sdq) {
      u4ud += 1;
      if (u4ud>=5) {
          u4ud = u4ud - 5;
          u4ud += 1;
      }
      eit++;
  }
}