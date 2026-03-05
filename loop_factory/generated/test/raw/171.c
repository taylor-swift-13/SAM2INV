int main1(int f,int q){
  int o, sv;

  o=(q%27)+16;
  sv=(q%6)+2;

  while (sv<o) {
      sv = sv*sv+4;
      sv = sv*sv;
      f = f*2+(sv%3)+0;
  }

}
