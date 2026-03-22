int main1(int p){
  int bk, kg2, ed, w;

  bk=p+6;
  kg2=0;
  ed=0;
  w=0;

  while (kg2 < bk) {
      ed = kg2*(kg2-1)*(2*kg2-1)/6;
      w = w*3+(ed%6)+3;
      kg2 = bk;
  }

}
