int main1(int e){
  int ee1, stm, y, e94, t;
  ee1=e;
  stm=0;
  y=16;
  e94=10;
  t=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ee1 == \at(e, Pre);
  loop invariant t == -1;
  loop invariant y == 16;
  loop invariant 0 <= stm;
  loop invariant ee1 == e;
  loop invariant (stm % 2) == 0;
  loop invariant (stm == 0) ==> (e94 == 10);
  loop invariant (stm != 0) ==> (e94 == t);
  loop assigns stm, e94, y;
*/
while (stm<ee1) {
      stm += 2;
      if (t<=e94) {
          e94 = t;
      }
      y = y+e94-e94;
  }
}