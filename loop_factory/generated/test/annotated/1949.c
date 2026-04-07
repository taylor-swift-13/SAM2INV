int main1(){
  int u, pqs, en8, tg;
  u=1;
  pqs=0;
  en8=1;
  tg=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= pqs;
  loop invariant pqs <= u;
  loop invariant u == 1;
  loop invariant tg - pqs >= 1;
  loop invariant tg - pqs >= u;
  loop invariant 1 - pqs <= en8;
  loop invariant en8 <= 1 + 2 * pqs;
  loop invariant tg <= u + 2 * pqs;
  loop assigns en8, pqs, tg;
*/
while (pqs < u) {
      en8 = en8 + 2*(en8 < tg) - 1*(en8 >= tg);
      pqs++;
      tg = tg + 1*(en8 < tg) + 2*(en8 >= tg);
  }
}