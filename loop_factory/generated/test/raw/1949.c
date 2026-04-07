int main1(){
  int u, pqs, en8, tg;

  u=1;
  pqs=0;
  en8=1;
  tg=u;

  while (pqs < u) {
      en8 = en8 + 2*(en8 < tg) - 1*(en8 >= tg);
      pqs++;
      tg = tg + 1*(en8 < tg) + 2*(en8 >= tg);
  }

}
