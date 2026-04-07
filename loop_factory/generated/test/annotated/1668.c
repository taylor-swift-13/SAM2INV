int main1(){
  int bq, rs40, jt11;
  bq=(1%18)+5;
  rs40=(1%15)+3;
  jt11=bq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rs40 == bq - 2;
  loop invariant jt11 == 6 + (6 - bq) * rs40 + ((6 - bq) * (5 - bq)) / 2;
  loop invariant 0 <= bq <= 6;
  loop assigns bq, rs40, jt11;
*/
while (bq!=0) {
      rs40 = rs40 - 1;
      bq -= 1;
      jt11 = jt11 + rs40;
  }
}