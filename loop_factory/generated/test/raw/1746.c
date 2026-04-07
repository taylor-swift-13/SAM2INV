int main1(){
  int szlp, c, i, pyrk, yw, ds;

  szlp=79;
  c=0;
  i=0;
  pyrk=0;
  yw=0;
  ds=7;

  while ((c < szlp)) {
      pyrk = pyrk + ds;
      yw = yw+(i%9);
      c = c + 1;
      ds = ds+(i%8);
  }

}
