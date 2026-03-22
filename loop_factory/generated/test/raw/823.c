int main1(int y){
  int wflu, r1os, s, ltl, e7, us;

  wflu=70;
  r1os=0;
  s=r1os;
  ltl=0;
  e7=0;
  us=(y%6)+2;

  while (e7<wflu) {
      ltl = ltl*us;
      s = s*us+3;
      e7 = e7 + 1;
      us = us+(s%2);
      us = us + r1os;
  }

}
