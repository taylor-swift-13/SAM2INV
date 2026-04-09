int main1(int t){
  int q, atz, tk, l9;
  q=t*5;
  atz=0;
  tk=13;
  l9=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tk == 13 + 3*atz;
  loop invariant l9 == 1 + 3*atz;
  loop invariant t + 12*atz == \at(t,Pre);
  loop invariant q == \at(t,Pre) * 5;
  loop invariant atz >= 0;
  loop invariant (q >= 0) ==> (atz <= q);
  loop assigns tk, atz, l9, t;
*/
while (atz < q) {
      tk = tk + 3;
      atz += 1;
      l9 = l9 + 3;
      t = t+l9-tk;
  }
}