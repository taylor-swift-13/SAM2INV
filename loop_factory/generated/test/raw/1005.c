int main1(){
  int n4ls, mi, ux9, wdn, ygc;

  n4ls=54;
  mi=n4ls;
  ux9=0;
  wdn=0;
  ygc=-1;

  while (1) {
      if (!(mi<=n4ls-1)) {
          break;
      }
      wdn += 1;
      ygc += 1;
      if (wdn>=10) {
          wdn = wdn - 10;
          ux9 = ux9 + 1;
      }
      mi++;
  }

}
