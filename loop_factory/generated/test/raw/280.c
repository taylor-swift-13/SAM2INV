int main1(int i,int u){
  int q, loh, czc;

  q=(u%10)+15;
  loh=0;
  czc=0;

  while (loh<q) {
      czc += 1;
      if (czc>=5) {
          czc = czc - 5;
          czc += 1;
      }
      loh += 1;
  }

}
