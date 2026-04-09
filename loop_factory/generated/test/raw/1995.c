int main1(){
  int ck, dtm, a, cerh;

  ck=1+22;
  dtm=0;
  a=1;
  cerh=3;

  while (dtm < ck) {
      a = (dtm += 1, a *= 2, a);
      cerh = cerh*3+(a%3)+1;
      dtm = ck;
  }

}
