int main1(int p){
  int o, cc, uyp, at, jf;

  o=p-9;
  cc=0;
  uyp=0;
  at=0;
  jf=o;

  while (at<=o-1) {
      at = at + 1;
      jf += cc;
      uyp += p;
  }

  while (1) {
      if (!(at>=1)) {
          break;
      }
      jf++;
      p += jf;
      at--;
  }

}
