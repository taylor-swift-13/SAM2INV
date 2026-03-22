int main1(){
  int hq7g, wx;
  hq7g=1+9;
  wx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= wx <= hq7g;
  loop assigns wx;
*/
for (; wx<=hq7g-1; wx += 1) {
  }
}