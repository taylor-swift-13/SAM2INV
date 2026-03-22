int main1(int s){
  int f9r, t42, jg, ko;

  f9r=(s%21)+13;
  t42=0;
  jg=s;
  ko=t42;

  for (; t42<=f9r-1; t42 += 1) {
      jg += 1;
      ko = ko + jg;
      s += t42;
      jg += 1;
  }

}
