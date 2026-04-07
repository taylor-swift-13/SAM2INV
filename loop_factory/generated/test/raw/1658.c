int main1(){
  int le, ms, ub, hk;

  le=1+7;
  ms=0;
  ub=ms;
  hk=le;

  while (ms < le) {
      ms += 1;
      ub = hk + ms;
      hk += ms;
  }

}
