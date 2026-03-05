int main1(int i,int u){
  int q, loh, czc;
  q=(u%10)+15;
  loh=0;
  czc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre);
  loop invariant u == \at(u, Pre);
  loop invariant q == (\at(u, Pre) % 10) + 15;
  loop invariant loh <= q;
  loop invariant 0 <= czc;
  loop invariant czc <= 4;
  loop invariant czc % 4 == loh % 4;
  loop invariant loh >= czc;
  loop assigns czc, loh;
*/
while (loh<q) {
      czc += 1;
      if (czc>=5) {
          czc = czc - 5;
          czc += 1;
      }
      loh += 1;
  }
}