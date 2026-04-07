int main1(){
  int thu, cp, mrr, l3, u;
  thu=1;
  cp=thu;
  mrr=0;
  l3=thu;
  u=thu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == thu + mrr * cp;
  loop invariant (mrr == 0) ==> (l3 == thu);
  loop invariant (mrr > 0) ==> (l3 == mrr - 1);
  loop invariant mrr <= thu;
  loop invariant 0 <= mrr;
  loop invariant 0 <= l3;
  loop invariant cp == thu;
  loop assigns l3, mrr, u;
*/
while (mrr<thu) {
      l3 = mrr;
      mrr++;
      u = u + cp;
  }
}