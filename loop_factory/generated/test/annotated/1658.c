int main1(){
  int le, ms, ub, hk;
  le=1+7;
  ms=0;
  ub=ms;
  hk=le;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ms == 0) ==> (ub == 0 && hk == le);
  loop invariant (ms > 0) ==> (ub == hk);
  loop invariant (0 <= ms);
  loop invariant (ms <= le);
  loop invariant ub <= hk;
  loop assigns ms, ub, hk;
*/
while (ms < le) {
      ms += 1;
      ub = hk + ms;
      hk += ms;
  }
}