int main1(){
  int swx7, wk, hm, q7u5, n2;
  swx7=(1%9)+20;
  wk=swx7;
  hm=0;
  q7u5=0;
  n2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n2 == (swx7 + wk) * q7u5;
  loop invariant hm == q7u5;
  loop invariant q7u5 <= swx7;
  loop invariant wk == swx7;
  loop invariant hm >= 0;
  loop assigns hm, n2, q7u5;
*/
while (q7u5<=swx7-1) {
      n2 = n2 + swx7;
      hm = hm + 1;
      q7u5 += 1;
      n2 += wk;
  }
}