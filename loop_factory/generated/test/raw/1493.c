int main1(int n){
  int o, eg, k, be, r;

  o=(n%7)+17;
  eg=2;
  k=o;
  be=eg;
  r=1;

  while (k<=o) {
      be = be*k;
      if (k<o) {
          r = r*k;
      }
      k += 1;
      n += eg;
  }

}
