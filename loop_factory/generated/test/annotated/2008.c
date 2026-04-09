int main1(){
  int io, gm, p3, m8ay, ye;
  io=1*3;
  gm=-1;
  p3=1;
  m8ay=io;
  ye=io;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m8ay == ye / p3;
  loop invariant p3 >= 1;
  loop invariant gm <= io;
  loop invariant ye == io;
  loop invariant io > 0;
  loop invariant (p3 == 1 || p3 % 2 == 0);
  loop assigns gm, p3, m8ay;
*/
while (1) {
      if (!(++gm < io)) {
          break;
      }
      p3 = p3*2;
      m8ay = ye/p3;
      gm = io;
  }
}