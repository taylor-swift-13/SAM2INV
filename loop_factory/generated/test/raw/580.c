int main1(){
  int o2, mi, di, a;

  o2=1;
  mi=1;
  di=0;
  a=0;

  while (mi<=o2) {
      di++;
      mi = 2*mi;
      a = a*4+(mi%7)+0;
  }

}
