int main1(){
  int rr, tq, kb2, lgg;
  rr=20;
  tq=rr;
  kb2=tq;
  lgg=tq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lgg >= 20;
  loop invariant lgg >= kb2;
  loop invariant kb2 >= 20;
  loop invariant (tq == 20) ==> (kb2 == 20 && lgg == 20);
  loop invariant (kb2 == 20) || (kb2 == 21);
  loop invariant (tq == 20) || (tq == 3);
  loop invariant (rr == 20);
  loop invariant lgg % 4 == 0;
  loop assigns kb2, lgg, tq;
*/
while (tq>3) {
      kb2 = kb2 + 1;
      lgg = lgg*4+(kb2%5)+3;
      tq = 3;
  }
}