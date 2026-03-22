int main1(){
  int iwn, qdia, i5, i;

  iwn=1;
  qdia=(1%40)+2;
  i5=0;
  i=-8;

  while (1) {
      if (!(qdia!=i5)) {
          break;
      }
      i5 = qdia;
      qdia = (qdia+iwn/qdia)/2;
      i = i + qdia;
  }

  while (1) {
      i5 = i5*2;
      iwn++;
      if (iwn>=qdia) {
          break;
      }
  }

}
