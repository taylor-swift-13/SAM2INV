int main1(int k){
  int jv1, qhr5, m;

  jv1=0;
  qhr5=(k%28)+10;
  m=0;

  while (1) {
      if (!(qhr5>jv1)) {
          break;
      }
      qhr5 = qhr5 - jv1;
      jv1 = jv1 + 1;
      m += qhr5;
  }

}
