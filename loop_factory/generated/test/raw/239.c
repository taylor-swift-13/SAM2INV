int main1(){
  int pavv, yjt, tmi, e;

  pavv=1*5;
  yjt=0;
  tmi=0;
  e=-1;

  while (e<pavv) {
      tmi = tmi + 1;
      e += 1;
      if ((yjt%4)==0) {
          tmi += tmi;
      }
  }

  while (1) {
      if (!(yjt-2>=0)) {
          break;
      }
      pavv += tmi;
      yjt++;
  }

}
