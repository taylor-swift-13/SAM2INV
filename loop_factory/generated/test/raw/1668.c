int main1(){
  int bq, rs40, jt11;

  bq=(1%18)+5;
  rs40=(1%15)+3;
  jt11=bq;

  while (bq!=0) {
      rs40 = rs40 - 1;
      bq -= 1;
      jt11 = jt11 + rs40;
  }

}
