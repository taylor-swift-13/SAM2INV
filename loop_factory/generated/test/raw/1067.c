int main1(int n,int b){
  int od, p6, na, si, e6;

  od=12;
  p6=0;
  na=0;
  si=0;
  e6=0;

  while (na<od) {
      if (e6<od) {
          si = na;
      }
      e6 += 1;
      na = na + 1;
  }

  while (p6<si) {
      na = na+e6*p6;
      od += p6;
      p6 = si;
  }

}
