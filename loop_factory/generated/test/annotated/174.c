int main1(){
  int k2v, r6;
  k2v=80;
  r6=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (r6 - 1) % 3 == 0;
  loop invariant r6 >= 1;
  loop invariant k2v == 80;
  loop invariant r6 <= k2v + 2;
  loop assigns r6;
*/
while (r6<=k2v) {
      r6 = r6 + 1;
      r6 += 2;
  }
}