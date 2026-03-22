int main1(int p,int e){
  int xuln, urun;
  xuln=(p%10)+17;
  urun=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((urun - 2) % 5 == 0);
  loop invariant (2 <= urun && urun <= xuln);
  loop invariant xuln == ((p % 10) + 17);
  loop invariant xuln == ((\at(p,Pre) % 10) + 17);
  loop assigns urun;
*/
for (; urun+5<=xuln; urun = urun + 5) {
  }
}