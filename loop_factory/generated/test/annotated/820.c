int main1(int e){
  int wk, z, ajk4, zh;
  wk=e*2;
  z=1;
  ajk4=wk;
  zh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ajk4 == e*2;
  loop invariant z == 1;
  loop invariant zh == 0 || zh == ajk4;
  loop invariant ajk4 == 2 * \at(e, Pre);
  loop invariant (wk == 2 * \at(e, Pre)) || (wk == 3);
  loop invariant (wk != 3) ==> (zh == 0);
  loop assigns zh, wk;
*/
while (z*4<=wk) {
      zh += ajk4;
      wk = (z*4)-1;
  }
}